-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_eq_68_69
-- name    : RollingProbeQN.Convex.eq_68_69
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:30:34.561204+00:00
-- url     : https://prove2.me/theorems/bb2d8506-fbe1-45c2-a228-58abe83ea48f
-- title:
--   (68)–(69) — explicit rate $\min\{2L_1R^2/(\sigma N^2),D_\sigma^3KR^2/(2N^3)\}$ and gradient count $1+3\lceil B_\varepsilon\rceil$
-- statement:
--   Under Assumption 2.1, run Algorithm 1 with $b=L_2R$ and $\sigma\in(0,1)$, and let $K=\chi(L_1+L_2R)$.
--
--   1. **(68)** For every completed horizon $N\ge1$,
--   $$f(x_N)-f^\star\ \le\ \min\Big\{\frac{2L_1R^2}{\sigma N^2},\ \frac{D_\sigma^3KR^2}{2N^3}\Big\}.$$
--   2. **(69)** For every $\varepsilon>0$, the $\varepsilon$-run (Steps 1–5) returns at some iteration, its output $\hat x$ satisfies $f(\hat x)-f^\star\le\varepsilon$, and the number $G_\varepsilon$ of gradient queries up to the return satisfies
--   $$G_\varepsilon\ \le\ 1+3\Big\lceil\min\Big\{\sqrt{\frac{2L_1R^2}{\sigma\varepsilon}},\ D_\sigma\Big(\frac{KR^2}{2\varepsilon}\Big)^{1/3}\Big\}\Big\rceil .$$
--
--   These are the explicit forms of (11) and (12), with constant $\max\{2/\sigma,D_\sigma^3/2\}$ depending only on $\sigma$.
--
--   Differences from the source:
--   - encoding: N ≥ 1 is a completed horizon → iterations 0, …, N − 1 are executed (Active); reason: a completed iteration is one that did not return at Step 1
--   - encoding: G_ε counts the gradient queries up to the return, including ∇f(x₀) (p. 52) → the length of allQueries (k + 1) at the first k with epsReturns; reason: the list holds x₀ and the three queries of each executed iteration, none for a return at a zero gradient (reading R4)
--   - reading: Algorithm 1 evaluates ∇f at the points it forms → the run is a function of an oracle G, taken to be gradient f; reason: the gradient is accessed only through oracle calls (reading R3)
--   - encoding: Step 1 returns x_k when ∇f(x_k) = 0; the iterates after a return do not exist → the run is frozen at the return; statements about an iteration assume it is executed (Active); reason: B_k, Ē_k, λ_k, y_k, r_k are formed only at executed iterations (reading R2)
--   - encoding: refreshed group i_k = (k mod χ) + 1, groups g_1, …, g_χ → 0-based label k % χ of grp : Fin d → Fin χ; reason: relabelling of the groups (reading R5)
--   - encoding: Π_Z clips the eigenvalues of a symmetric matrix to [0, L₁] → clipZ L₁, the functional calculus of t ↦ min (max t 0) L₁ (0 on non-symmetric input); reason: the same map on symmetric matrices, the only input it receives (reading R6)
--   - encoding: a partition g₁, …, g_χ of [d] → a surjective map grp : Fin d → Fin χ with 0 < χ; reason: a partition has no empty block (reading R7)
--   - encoding: the while loop of Subroutine 1.1 → a guarded bisection pass iterated ⌈4 log(L₁/Ē_k)/log 2⌉ + 1 times; reason: the loop ends within that many passes (Lemma E.6's count) and further passes change nothing (reading R8)
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Appendix E.3, (68), p. 51, constant p. 52; Appendix E.4, (69), p. 52

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_Assumption21
import Definitions.Def_RollingProbeQN_Convex_Active
import Definitions.Def_RollingProbeQN_Convex_allQueries
import Definitions.Def_RollingProbeQN_Convex_epsReturns
import Definitions.Def_RollingProbeQN_Convex_epsOutput
import Definitions.Def_RollingProbeQN_Convex_Dsigma

namespace RollingProbeQN.Convex

/-- **The explicit rate (68) and the explicit gradient count (69).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Appendix E.3, (68), p. 51: "`f(x_N) − f★ ≤ min{2L1R²/(σN²), D_σ³KR²/(2N³)}`, which is (11) with
`k = N`, `K = χ(L1 + L2R)` and the constant `max{2/σ, D_σ³/2}`" (p. 52); Appendix E.4, p. 52:
"Algorithm 1 returns `x_{k+1}` as soon as `A_{k+1} ≥ R²/(2ε)`; by Lemma D.1(i),
`f(x_{k+1}) − f★ ≤ R²/(2A_{k+1}) ≤ ε`. […] A return at `g_k = 0` is exact." and (69):
"`G_ε ≤ 1 + 3⌈min{√(2L1R²/(σε)), D_σ(KR²/(2ε))^{1/3}}⌉`".

Under Assumption 2.1 with `b = L₂R`: (68) for every completed horizon `N ≥ 1`; and for every
`ε > 0` the ε-run returns at some iteration `k` (its first return), its output is `ε`-accurate, and the
number of oracle calls up to the return is at most `1 + 3⌈B_ε⌉`.

**Formalization Note.** The run is `run cfg (gradient f) x₀` with `cfg = ⟨grp, S, L₁, L₂, L₂R, σ⟩`. A
completed horizon is: iterations `0, …, N − 1` executed (`Active`). The ε-run is the run stopped at
the first `k` with `epsReturns`; its output is `epsOutput k` and its gradient count is the length of
`allQueries (k + 1)`, which includes `∇f(x₀)` (reading R4) and nothing for a return at a zero
gradient. `⌈·⌉` is `Nat.ceil` of a positive real. -/
theorem eq_68_69 {d χ : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {L₁ L₂ R σ : ℝ}
    {S : Set (Fin d × Fin d)} {grp : Fin d → Fin χ} {x₀ xstar : EuclideanSpace ℝ (Fin d)}
    (hA : Assumption21 d χ f L₁ L₂ R S grp x₀ xstar) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    let cfg : Config d χ := ⟨grp, S, L₁, L₂, L₂ * R, σ⟩
    let K : ℝ := χ * (L₁ + L₂ * R)
    (∀ N : ℕ, 1 ≤ N → (∀ k < N, Active cfg (gradient f) x₀ k) →
      f (run cfg (gradient f) x₀ N).x - f xstar ≤
        min (2 * L₁ * R ^ 2 / (σ * (N : ℝ) ^ 2)) (Dsigma σ ^ 3 * K * R ^ 2 / (2 * (N : ℝ) ^ 3))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ k : ℕ,
      epsReturns cfg (gradient f) x₀ R ε k ∧
      (∀ j < k, ¬ epsReturns cfg (gradient f) x₀ R ε j) ∧
      f (epsOutput cfg (gradient f) x₀ k) - f xstar ≤ ε ∧
      (allQueries cfg (gradient f) x₀ (k + 1)).length ≤
        1 + 3 * ⌈min (Real.sqrt (2 * L₁ * R ^ 2 / (σ * ε)))
          (Dsigma σ * (K * R ^ 2 / (2 * ε)) ^ ((1 : ℝ) / 3))⌉₊) := by sorry

end RollingProbeQN.Convex
