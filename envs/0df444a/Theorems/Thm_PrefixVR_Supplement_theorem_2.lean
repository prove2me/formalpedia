-- Prove2me | Theorems.Thm_PrefixVR_Supplement_theorem_2
-- name    : PrefixVR.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:51:51.577305+00:00
-- url     : https://prove2.me/theorems/0160e6cd-5190-433b-b2b9-69c652f0c3cb
-- title:
--   Theorem 2 — $\mathbb E\|\nabla f(x_\tau)\|^2\le 4K\Delta_f/T$ with $K=L_f+\sqrt{2n}\,\delta$, and $n+5T$ queries for accuracy $\epsilon^2$
-- statement:
--   Let $n\ge1$ and let $f_1,\dots,f_n:\mathbb R^d\to\mathbb R$ have gradients $\nabla f_i$ and satisfy **Assumption 3** with constants $L_f>0$, $\delta\ge0$ ($f=\frac1n\sum_i f_i$ is $L_f$-smooth and $\frac1n\sum_i\|\nabla f_i(x)-\nabla f_i(y)-\nabla f(x)+\nabla f(y)\|^2\le\delta^2\|x-y\|^2$), and let $f$ satisfy **Assumption 2** ($f_*=\inf f>-\infty$, $\Delta_f=f(x_1)-f_*$). Run Algorithm 1 from $x_1$ with
--   $$
--   K:=L_f+\sqrt{2n}\,\delta,\qquad \eta=\frac1{2K}.
--   $$
--   Then:
--   1. for every $T\ge1$, $$\mathbb E\,\|\nabla f(x_\tau)\|^2\le\frac{4K\Delta_f}{T},\qquad(11)$$ the expectation being over the uniform output index $\tau\in[T]$ and all estimator samples;
--   2. for every $\epsilon>0$, the horizon $T=\max\{1,\lceil4K\Delta_f/\epsilon^2\rceil\}$ gives $\mathbb E\|\nabla f(x_\tau)\|^2\le\epsilon^2$, and on every outcome the method makes at most $n+5T$ component-gradient queries, so that $N_{\rm grad}=O\big(n+(L_f+\sqrt n\,\delta)\Delta_f/\epsilon^2\big)$ (12).
--
--   The bound separates the smoothness of the average from the centered variation $\delta$ of component-gradient differences; when the components differ by linear terms, $\delta=0$ and the rate is that of exact gradient descent. Assumption 1 is not needed.
--
--   **Formalization Note** Assumption 3 is the published `PrefixVR.Assumption3`; Algorithm 1, its sample space, expectation, output $x_\tau$ and query log are the published `PrefixVR.run`, `Sample`, `expect`, `output`, `queryLog`; $\nabla f$ is Mathlib's `gradient`. The printed $\sqrt2n\delta$ is $\sqrt{2n}\,\delta$.
--
--   Differences from the source:
--   - encoding: Assumption 3: f is L_f-smooth, L_f > 0, δ ≥ 0 and (2) holds → the published PrefixVR.Assumption3 fi gf Lf δ (each fᵢ has gradient gf i x everywhere; Lf > 0; IsBetaSmooth f (gradAvg gf) Lf; 0 ≤ δ; Variation gf δ); reason: (2) names the gradients ∇fᵢ, so they exist; the gradient of f is then their average, so the smoothness clause is exactly L_f-smoothness of f
--   - encoding: Assumption 2: f_* := inf f > −∞, Δ_f = f(x₁) − f_* → BddBelow (Set.range f), Δ_f = f x₁ − ⨅ x, f x; reason: a real infimum of a set bounded below is the true infimum
--   - encoding: the expectation over τ and all estimator samples of Algorithm 1 → the published uniform average expect over the finite sample space Sample n T (τ and the draws (j_t, i_t), t ≤ T, with dummy or unused coordinates where nothing is drawn); reason: independent uniform draws on finite sets have the uniform product law; unused coordinates change no expectation
--   - encoding: N_grad, the number of component-gradient queries → the length of the published query log queryLog on every outcome; reason: Algorithm 1 reaches ∇fᵢ only through the logging oracle; one evaluation is one entry
--   - reading: an expected squared gradient norm of at most ε² requires T = max{1, ⌈4KΔ_f/ε²⌉} and N_grad = O(n + (L_f + √nδ)Δ_f/ε²) (12) → for every ε > 0 and T = max{1, ⌈4KΔ_f/ε²⌉₊}: 𝔼‖∇f(x_τ)‖² ≤ ε² and N_grad ≤ n + 5T on every outcome; reason: 'requires' states that this T suffices; App. C p.16 proves N_grad ≤ n + 5T, which gives (12) since n + 5T ≤ n + 10 + 20(L_f + √2·√n δ)Δ_f/ε²
--   - encoding: components i ∈ [n] → Fin n with NeZero n, paper index i is i − 1; reason: Lean convention; n ≥ 1 is the standing setting of a finite sum
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), §4, Theorem 2, Eqs. (11)–(12), p.7 (PDF p.7); proof App. C, p.16

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_KatyushaNs_favg
import Definitions.Def_PrefixVR_Variation
import Definitions.Def_PrefixVR_Assumption3
import Definitions.Def_PrefixVR_step
import Definitions.Def_PrefixVR_Sample
import Definitions.Def_PrefixVR_run

namespace PrefixVR.Supplement

open PrefixVR

/-- **Theorem 2.** Jiang, Wang, Yang, Li, Zhang, *Memory-efficient Finite-sum Optimization without
Full Gradient Refreshes* (manuscript, sha256 ed33106a…), §4, Theorem 2, Eqs. (11)–(12), p.7:
"Under Assumptions 2 and 3, let K := L_f + √2nδ, η = 1/(2K). For Algorithm 1, we can ensure
𝔼‖∇f(x_τ)‖² ≤ 4KΔ_f/T. Consequently, an expected squared gradient norm of at most ε² requires
T = max{1, ⌈4KΔ_f/ε²⌉} and N_grad = O(n + (L_f + √nδ)Δ_f/ε²)." Proof: App. C, p.16.

For every `n ≥ 1`, `d`, components `fᵢ` with gradient maps `gf i = ∇fᵢ` satisfying Assumption 3
with constants `L_f, δ`, `f = (1/n) ∑ fᵢ` bounded below, and every `x₁`, Algorithm 1 with
`K = L_f + √(2n) δ` and `η = 1/(2K)` satisfies:
1. for every `T ≥ 1`, `𝔼‖∇f(x_τ)‖² ≤ 4K(f(x₁) − f_*)/T` (11);
2. for every `ε > 0` and `T = max{1, ⌈4KΔ_f/ε²⌉}`, `𝔼‖∇f(x_τ)‖² ≤ ε²` and, on every outcome,
   the number of component-gradient queries is at most `n + 5T` (the explicit form of (12),
   App. C, "Query and memory counts", p.16).

**Formalization Note.** Assumption 3 is the published `PrefixVR.Assumption3 fi gf Lf δ`;
Assumption 2 is `BddBelow (Set.range f)` with `f_* = ⨅ x, f x`; `f = KatyushaNs.favg fi`; `∇f` is
Mathlib's `gradient`. Algorithm 1, its sample space, expectation, output `x_τ` and query log are
the published `PrefixVR.run` / `Sample` / `expect` / `output` / `queryLog`. "√2nδ" is `√(2n)·δ`. -/
theorem theorem_2 {n d : ℕ} [NeZero n] (fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gf : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (Lf δ : ℝ)
    (hA3 : Assumption3 fi gf Lf δ)
    (hA2 : BddBelow (Set.range (KatyushaNs.favg fi)))
    (x₁ : EuclideanSpace ℝ (Fin d)) :
    let K := Lf + Real.sqrt (2 * n) * δ
    let η := 1 / (2 * K)
    let Δf := KatyushaNs.favg fi x₁ - ⨅ x, KatyushaNs.favg fi x
    (∀ T : ℕ, 1 ≤ T →
      expect (fun ω : Sample n T => ‖gradient (KatyushaNs.favg fi) (output gf η x₁ ω)‖ ^ 2)
        ≤ 4 * K * Δf / T) ∧
    (∀ ε : ℝ, 0 < ε → ∀ T : ℕ, T = max 1 ⌈4 * K * Δf / ε ^ 2⌉₊ →
      expect (fun ω : Sample n T => ‖gradient (KatyushaNs.favg fi) (output gf η x₁ ω)‖ ^ 2)
          ≤ ε ^ 2 ∧
        ∀ ω : Sample n T, (queryLog gf η x₁ ω).length ≤ n + 5 * T) := by sorry

end PrefixVR.Supplement
