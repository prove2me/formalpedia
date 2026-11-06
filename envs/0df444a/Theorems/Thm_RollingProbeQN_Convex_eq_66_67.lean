-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_eq_66_67
-- name    : RollingProbeQN.Convex.eq_66_67
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:28:51.369924+00:00
-- url     : https://prove2.me/theorems/5117391e-5dde-4cf0-ab68-2a6f42246bfe
-- title:
--   (66)–(67) — at most $d_\sigma(Ks)^{1/3}$ iterations per mass scale, hence $A_N\ge N^3/(D_\sigma^3K)$
-- statement:
--   Under Assumption 2.1, run Algorithm 1 with $b=L_2R$ and $\sigma\in(0,1)$, and let $K=\chi(L_1+L_2R)$. Let $N\ge1$ be a completed horizon (iterations $0,\dots,N-1$ executed).
--
--   1. **(66)** For every $s>0$ such that the scale $I=\{k\in\{0,\dots,N-1\}:\ s\le A_{k+1}<2s\}$ is nonempty,
--   $$|I|\ \le\ d_\sigma\,(Ks)^{1/3}.$$
--   2. **(67)**
--   $$A_N\ \ge\ \frac{N^3}{D_\sigma^3K}.$$
--
--   The constants $d_\sigma,D_\sigma$ of (65) depend only on $\sigma$. The cubic growth of the mass is the curvature branch of Theorem 3.1.
--
--   Differences from the source:
--   - encoding: N ≥ 1 is a completed horizon (p. 49) → iterations 0, …, N − 1 are executed (Active); reason: a completed iteration is one that did not return at Step 1
--   - encoding: Step 1 returns x_k when ∇f(x_k) = 0; the iterates after a return do not exist → the run is frozen at the return; statements about an iteration assume it is executed (Active); reason: B_k, Ē_k, λ_k, y_k, r_k are formed only at executed iterations (reading R2)
--   - encoding: refreshed group i_k = (k mod χ) + 1, groups g_1, …, g_χ → 0-based label k % χ of grp : Fin d → Fin χ; reason: relabelling of the groups (reading R5)
--   - encoding: Π_Z clips the eigenvalues of a symmetric matrix to [0, L₁] → clipZ L₁, the functional calculus of t ↦ min (max t 0) L₁ (0 on non-symmetric input); reason: the same map on symmetric matrices, the only input it receives (reading R6)
--   - encoding: a partition g₁, …, g_χ of [d] → a surjective map grp : Fin d → Fin χ with 0 < χ; reason: a partition has no empty block (reading R7)
--   - encoding: the while loop of Subroutine 1.1 → a guarded bisection pass iterated ⌈4 log(L₁/Ē_k)/log 2⌉ + 1 times; reason: the loop ends within that many passes (Lemma E.6's count) and further passes change nothing (reading R8)
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Appendix E.3, (66) and (67), p. 51

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_Assumption21
import Definitions.Def_RollingProbeQN_Convex_Active
import Definitions.Def_RollingProbeQN_Convex_Dsigma

namespace RollingProbeQN.Convex

/-- **The local count (66) and the mass bound (67).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Appendix E.3, (66) and (67), p. 51: "we have the explicit local count `|I| ≤ d_σ(Ks)^{1/3}`"
for every scale `I = {k ∈ {0, …, N − 1} : s ≤ A_{k+1} < 2s}` with `s > 0` and `I` nonempty (p. 49);
"We conclude that `A_N ≥ N³/(D_σ³ K)`." Here `K = χ(L1 + L2R)`, `b = L2R` and `N ≥ 1` is a completed
horizon.

**Formalization Note.** The run is `run cfg (gradient f) x₀` with `cfg = ⟨grp, S, L₁, L₂, L₂R, σ⟩`.
"`N ≥ 1` is a completed horizon" (p. 49) is: iterations `0, …, N − 1` are executed (`Active`). The
constants `d_σ, D_σ` are those of (65) (`dsigma`, `Dsigma`) and depend only on `σ`. -/
theorem eq_66_67 {d χ : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {L₁ L₂ R σ : ℝ}
    {S : Set (Fin d × Fin d)} {grp : Fin d → Fin χ} {x₀ xstar : EuclideanSpace ℝ (Fin d)}
    (hA : Assumption21 d χ f L₁ L₂ R S grp x₀ xstar) (hσ0 : 0 < σ) (hσ1 : σ < 1) (N : ℕ)
    (hN : 1 ≤ N)
    (hact : ∀ k < N, Active (⟨grp, S, L₁, L₂, L₂ * R, σ⟩ : Config d χ) (gradient f) x₀ k) :
    let cfg : Config d χ := ⟨grp, S, L₁, L₂, L₂ * R, σ⟩
    let K : ℝ := χ * (L₁ + L₂ * R)
    (∀ s : ℝ, 0 < s →
      ((Finset.range N).filter (fun k => s ≤ (run cfg (gradient f) x₀ (k + 1)).A ∧
          (run cfg (gradient f) x₀ (k + 1)).A < 2 * s)).Nonempty →
      (((Finset.range N).filter (fun k => s ≤ (run cfg (gradient f) x₀ (k + 1)).A ∧
          (run cfg (gradient f) x₀ (k + 1)).A < 2 * s)).card : ℝ) ≤
        dsigma σ * (K * s) ^ ((1 : ℝ) / 3)) ∧
    (N : ℝ) ^ 3 / (Dsigma σ ^ 3 * K) ≤ (run cfg (gradient f) x₀ N).A := by sorry

end RollingProbeQN.Convex
