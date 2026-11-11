-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_relaxed_primal_dual
-- name    : SparsestCutOracle.Main.relaxed_primal_dual
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:44:40.568921+00:00
-- url     : https://prove2.me/theorems/8b1953c0-f3d9-4dfd-8e1b-16ef63e09785
-- title:
--   Lemma 9 — The relaxed primal-dual guarantee
-- statement:
--   Here $\Pi=\sum_i\pi(i)$ and $D_\pi=\operatorname{diag}(\pi)$. The constraint matrices and dual coordinates are those of SDP 2, including both signs of the normalization constraint.
--
--   Let $\pi>0$, $\alpha,\rho>0$, and $\eta=\alpha/(20\rho\Pi)\le1$. Consider the actual multiplicative-weights iterates of Algorithm 1 with an arbitrary sequence of nonnegative dual multipliers $y^{(t)}$, auxiliary matrices $F^{(t)}$, and nondecreasing objectives $C^{(t)}$. Suppose every response has value at least $\alpha$, satisfies $F^{(t)}\preceq C^{(t+1)}$, has width $\rho$ relative to $D_\pi$, and obeys $Z^{(t)}\mathbin\bullet X^{(t)}\ge-\alpha/10$. If
--
--   $$T\ge\left\lceil\frac{400\rho^2\Pi^2\log n}{\alpha^2}\right\rceil,$$
--
--   then the average dual variables, corrected by $\alpha/(5\Pi)$ on the upper-normalization constraint, are nonnegative, feasible for the final objective, and have value at least $4\alpha/5$. This is a claim about the computed iterates and corrected average, rather than arbitrary matrices pinned by the desired conclusion.
--
--   Differences from the source:
--   - encoding: iterations t=1,…,T and final objective C^(T+1) → iterations t=0,…,T−1 and final objective C T; reason: the initial exponential is I/n; the sum in the t-th iterate ranges strictly over earlier feedback matrices
--   - encoding: the generalized oracle dual solution → explicit path, centering, and both normalization multipliers for SDP 2; reason: no restriction to x=α/Π or to zero upper-normalization multipliers is imposed
--   - generalization: the graph Laplacian objectives in the sparsest-cut application → arbitrary nondecreasing matrix objectives satisfying the same auxiliary and width bounds; reason: the generalized primal-dual proof on pp.15–16 and p.57 uses only these Loewner comparisons; graph Laplacians are included
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), p. 26, Lemma 9; proof p. 57; Algorithm 1 p. 15

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_MMW

namespace SparsestCutOracle.Main

/-- Lemma 9, p.26 (proof p.57). The final dual is feasible for C(T), the updated objective. -/
theorem relaxed_primal_dual {n : ℕ} (hn : 2 ≤ n) (cP : ℕ) (hcP : 1 ≤ cP)
    (π : Fin n → ℝ) (hπ : ∀ v, 0 < π v)
    (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ)
    (hη : α / (20 * ρ * totalWeight π) ≤ 1)
    (T : ℕ) (hT : ⌈400 * ρ ^ 2 * totalWeight π ^ 2 * Real.log n / α ^ 2⌉₊ ≤ T)
    (y : ℕ → DualVariables n) (F C : ℕ → Mat n)
    (hdual : ∀ t < T, DualNonnegative cP (y t) ∧ α ≤ dualValue π (y t))
    (hmonotone : ∀ t < T, LePSD (C t) (C (t + 1)))
    (haux : ∀ t < T, LePSD (F t) (C (t + 1)))
    (hwidth : ∀ t < T, Width π ρ (F t - dualMatrix π (y t)))
    (hfeedback : ∀ t < T,
      -α / 10 ≤ dot (F t - dualMatrix π (y t))
        (mmwIterate π ρ (α / (20 * ρ * totalWeight π))
          (fun s => F s - dualMatrix π (y s)) t)) :
    let ystar := correctedAverage π α y T
    DualNonnegative cP ystar ∧ LePSD (dualMatrix π ystar) (C T) ∧
    (4 / 5 : ℝ) * α ≤ dualValue π ystar := by sorry

end SparsestCutOracle.Main
