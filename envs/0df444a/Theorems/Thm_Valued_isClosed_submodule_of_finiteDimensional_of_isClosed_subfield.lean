-- Prove2me | Theorems.Thm_Valued_isClosed_submodule_of_finiteDimensional_of_isClosed_subfield
-- name    : Valued.isClosed_submodule_of_finiteDimensional_of_isClosed_subfield
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/6e4ce10d-8195-5e7c-8cc0-fb38f9abe492
-- title:
--   Finite-dimensional subspaces over a closed valued subfield are closed
-- statement:
--   Let $K$ be a field equipped with a valuation $v$ taking values in a linearly ordered commutative group with zero $\Gamma_0$ (via a `Valued` structure, so that $K$ carries the associated topology and uniformity), and assume $K$ is complete. Assume the archimedean-type condition `hrk`: for all $x, y \in K$ with $v(x) < 1$ and $y \neq 0$ there is a natural number $n$ with $v(x)^n \le v(y)$. Let $K_0'$ be a subfield of $K$ whose underlying subset is closed in $K$, and assume $v$ is non-trivial on $K_0'$ in the sense that there exists $x \in K_0'$ with $x \neq 0$ and $v(x) < 1$. Let $V$ be a $K_0'$-submodule of $K$ (that is, a $K_0'$-subspace of $K$ regarded as a $K_0'$-vector space) which is finite-dimensional over $K_0'$. Then the underlying subset of $V$ is closed in $K$.
--
--   This is the standard fact that finite-dimensional subspaces of a topological vector space over a complete non-trivially valued base field are closed, stated here for subspaces of a complete rank-one valued field $K$ over a closed subfield $K_0'$ on which the valuation is non-trivial. It is used in the construction of two closed subfields of a completion whose intersection is a prescribed rational closure, in [`ValuationSubring.exists_two_closed_subfields_completion_inf_eq_ratClosure_of_liesOverPrime`](thm.html#ValuationSubring.exists_two_closed_subfields_completion_inf_eq_ratClosure_of_liesOverPrime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Valued_isClosed_submodule_of_finiteDimensional_of_isClosed_subfield.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Valued.isClosed_submodule_of_finiteDimensional_of_isClosed_subfield
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (K₀' : Subfield K) (hcl : IsClosed (K₀' : Set K)) (hnt : ∃ x ∈ K₀', x ≠ 0 ∧ Valued.v x < 1)
    (V : Submodule ↥K₀' K) [FiniteDimensional ↥K₀' ↥V] :
    IsClosed (V : Set K) := by sorry
