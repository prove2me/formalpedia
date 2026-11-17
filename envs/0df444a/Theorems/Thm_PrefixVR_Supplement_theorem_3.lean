-- Prove2me | Theorems.Thm_PrefixVR_Supplement_theorem_3
-- name    : PrefixVR.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:52:28.743881+00:00
-- url     : https://prove2.me/theorems/009cc3e5-3c1c-4614-a6c5-9f626afdd5a5
-- title:
--   Theorem 3 — under PL, $\mathbb E[f(x_{T+1})-f_*]\le(1-\rho)^T\Delta_f$ with $\rho=\min\{\mu\eta,1/(4n)\}$
-- statement:
--   Let $n\ge1$ and let $f_1,\dots,f_n$ satisfy **Assumption 3** with $L_f>0$, $\delta\ge0$, and let $f=\frac1n\sum_i f_i$ satisfy **Assumption 2** ($f_*=\inf f>-\infty$, $\Delta_f=f(x_1)-f_*$) and **Assumption 4** (the PL condition $\frac12\|\nabla f(x)\|^2\ge\mu(f(x)-f_*)$ with $\mu>0$). Run Algorithm 1 from $x_1$ with
--   $$
--   \eta=\frac1{2(L_f+\sqrt{2n}\,\delta)},\qquad \rho=\min\Big\{\mu\eta,\ \frac1{4n}\Big\}.
--   $$
--   Then:
--   1. for every $T\ge1$ the last iterate satisfies $$\mathbb E\big[f(x_{T+1})-f_*\big]\le(1-\rho)^T\Delta_f;\qquad(14)$$
--   2. for $0<\varepsilon_f<\Delta_f$, the horizon $$T=\Big\lceil\max\Big\{\frac{2(L_f+\sqrt{2n}\,\delta)}{\mu},\,4n\Big\}\log\frac{\Delta_f}{\varepsilon_f}\Big\rceil$$ gives $\mathbb E[f(x_{T+1})-f_*]\le\varepsilon_f$ with at most $n+5T$ component-gradient queries on every outcome, so the sample complexity is $O\big(n+[n+(L_f+\sqrt n\,\delta)/\mu]\log(\Delta_f/\varepsilon_f)\big)$ (15);
--   3. the per-update query bound is unchanged: every update makes at most five component-gradient queries, each at $x_t$ or $x_{t+1}$.
--
--   This is a linear rate for the same memory-light estimator, at the last iterate rather than a randomly selected one.
--
--   **Formalization Note** The algorithm and its logs are the published `PrefixVR.run`, `xIter`, `queryLog`, `updateLog`; $x_{T+1}$ is `xIter … (T + 1)`, and the expectation is the published `expect` over `Sample n T`. $\log$ is `Real.log` and $\lceil\cdot\rceil$ is `Nat.ceil`. The memory bound is read structurally, as in Theorem 1.
--
--   Differences from the source:
--   - encoding: Assumption 3: f is L_f-smooth, L_f > 0, δ ≥ 0 and (2) holds → the published PrefixVR.Assumption3 fi gf Lf δ (each fᵢ has gradient gf i x everywhere; Lf > 0; IsBetaSmooth f (gradAvg gf) Lf; 0 ≤ δ; Variation gf δ); reason: (2) names the gradients ∇fᵢ, so they exist; the gradient of f is then their average, so the smoothness clause is exactly L_f-smoothness of f
--   - encoding: Assumption 2: f_* := inf f > −∞, Δ_f = f(x₁) − f_* → BddBelow (Set.range f), Δ_f = f x₁ − ⨅ x, f x; reason: a real infimum of a set bounded below is the true infimum
--   - encoding: Assumption 4: μ > 0 and ½‖∇f(x)‖² ≥ μ(f(x) − f_*) for all x → Assumption4 f μ, with the same f_* = ⨅ y, f y; reason: the real infimum is f_* under Assumption 2, which is assumed
--   - encoding: the expectation over τ and all estimator samples of Algorithm 1 → the published uniform average expect over the finite sample space Sample n T (τ and the draws (j_t, i_t), t ≤ T, with dummy or unused coordinates where nothing is drawn); reason: independent uniform draws on finite sets have the uniform product law; unused coordinates change no expectation
--   - encoding: the last iterate x_{T+1} after T updates (Algorithm 1 returns x_{T+1} under Theorem 3) → xIter gf η x₁ ω (T + 1) on the horizon-T sample space, whose τ coordinate is drawn and unused; reason: the trajectory does not use τ, so the extra coordinate changes no expectation
--   - reading: to ensure expected gap ≤ ε_f we require T = ⌈max{2(L_f+√2nδ)/μ, 4n} log(Δ_f/ε_f)⌉ and the sample complexity is O(n + [n + (L_f+√nδ)/μ] log(Δ_f/ε_f)) (15) → for every 0 < ε_f < Δ_f and T = ⌈max{2K/μ, 4n}·Real.log(Δ_f/ε_f)⌉₊: 𝔼[f(x_{T+1}) − f_*] ≤ ε_f and the query log has length ≤ n + 5T on every outcome; reason: 'require' states that this T suffices; (63), p.19, gives N_grad ≤ n + 5T_{ε_f}, which yields (15)
--   - reading: the per-update query and memory bounds remain unchanged → for every horizon, outcome and update 1 ≤ t ≤ T, at most five queries, each at x_t or x_{t+1}; memory read structurally (Algorithm 1 is unchanged), no separate conjunct; reason: §3.4 states the per-update bound in exactly this form; there is no machine model in which to state O(d) memory
--   - encoding: components i ∈ [n] → Fin n with NeZero n, paper index i is i − 1; reason: Lean convention; n ≥ 1 is the standing setting of a finite sum
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), §5, Theorem 3, Eqs. (14)–(15), p.8 (PDF p.8); proof App. D, pp.17–19, (61), (63)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_KatyushaNs_favg
import Definitions.Def_PrefixVR_Variation
import Definitions.Def_PrefixVR_Assumption3
import Definitions.Def_PrefixVR_step
import Definitions.Def_PrefixVR_Sample
import Definitions.Def_PrefixVR_run
import Definitions.Def_PrefixVR_Supplement_Assumption4

namespace PrefixVR.Supplement

open PrefixVR

/-- **Theorem 3.** Jiang, Wang, Yang, Li, Zhang, *Memory-efficient Finite-sum Optimization without
Full Gradient Refreshes* (manuscript, sha256 ed33106a…), §5, Theorem 3, Eqs. (14)–(15), p.8:
"Under Assumptions 2, 3, and 4, run Algorithm 1 with η = 1/(2(L_f + √2nδ)), ρ = min{μη, 1/(4n)}.
The last iterate after T updates satisfies 𝔼[f(x_{T+1}) − f_*] ≤ (1 − ρ)^T Δ_f. For
0 < ε_f < Δ_f, to ensure expected function gap at most ε_f, we require
T = ⌈max{2(L_f + √2nδ)/μ, 4n} log(Δ_f/ε_f)⌉ and the sample complexity is
O(n + [n + (L_f + √nδ)/μ] log(Δ_f/ε_f)). The per-update query and memory bounds remain
unchanged." Proof: App. D, pp.17–19, (61), (63).

With `K = L_f + √(2n) δ`, `η = 1/(2K)`, `ρ = min{μη, 1/(4n)}`, Algorithm 1 satisfies:
1. for every `T ≥ 1`, `𝔼[f(x_{T+1}) − f_*] ≤ (1 − ρ)^T Δ_f` (14), at the last iterate;
2. for every `0 < ε_f < Δ_f` and `T = ⌈max{2K/μ, 4n} log(Δ_f/ε_f)⌉`,
   `𝔼[f(x_{T+1}) − f_*] ≤ ε_f` and, on every outcome, at most `n + 5T` component-gradient queries
   (the explicit form of (15), (63) p.19);
3. for every horizon `T`, outcome and update `1 ≤ t ≤ T`, the update makes at most five queries,
   each at `x_t` or `x_{t+1}` (the per-update query bound of §3.4, unchanged).

**Formalization Note.** Assumption 3 is the published `PrefixVR.Assumption3`, Assumption 2 is
`BddBelow (Set.range f)` with `f_* = ⨅ x, f x`, Assumption 4 is `Assumption4 f μ` (same `f_*`).
The last iterate `x_{T+1}` (Algorithm 1, line 22: "or x_{T+1} under the PL guarantee of
Theorem 3") is `xIter gf η x₁ ω (T + 1)` on the horizon-`T` sample space, whose output-index
coordinate is drawn and unused. `log` is `Real.log`, `⌈·⌉` is `Nat.ceil`. The memory bound is
read structurally, as in Theorem 1: Algorithm 1 is unchanged (the iteration of `step` on the
four-vector record `State d`). -/
theorem theorem_3 {n d : ℕ} [NeZero n] (fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gf : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (Lf δ μ : ℝ)
    (hA3 : Assumption3 fi gf Lf δ)
    (hA2 : BddBelow (Set.range (KatyushaNs.favg fi)))
    (hA4 : Assumption4 (KatyushaNs.favg fi) μ)
    (x₁ : EuclideanSpace ℝ (Fin d)) :
    let K := Lf + Real.sqrt (2 * n) * δ
    let η := 1 / (2 * K)
    let ρ := min (μ * η) (1 / (4 * (n : ℝ)))
    let fstar := ⨅ x, KatyushaNs.favg fi x
    let Δf := KatyushaNs.favg fi x₁ - fstar
    (∀ T : ℕ, 1 ≤ T →
      expect (fun ω : Sample n T => KatyushaNs.favg fi (xIter gf η x₁ ω (T + 1)) - fstar)
        ≤ (1 - ρ) ^ T * Δf) ∧
    (∀ εf : ℝ, 0 < εf → εf < Δf →
      ∀ T : ℕ, T = ⌈max (2 * K / μ) (4 * (n : ℝ)) * Real.log (Δf / εf)⌉₊ →
      expect (fun ω : Sample n T => KatyushaNs.favg fi (xIter gf η x₁ ω (T + 1)) - fstar)
          ≤ εf ∧
        ∀ ω : Sample n T, (queryLog gf η x₁ ω).length ≤ n + 5 * T) ∧
    (∀ T : ℕ, ∀ ω : Sample n T, ∀ t : ℕ, 1 ≤ t → t ≤ T →
      (updateLog gf η x₁ ω t).length ≤ 5 ∧
      ∀ q ∈ updateLog gf η x₁ ω t, q.2 = xIter gf η x₁ ω t ∨ q.2 = xIter gf η x₁ ω (t + 1)) := by sorry

end PrefixVR.Supplement
