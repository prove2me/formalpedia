-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P13_proposition_4_1
-- name    : QAlgorithms.Papers.Independent.Intake100.P13.proposition_4_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:08:56.072865+00:00
-- url     : https://prove2.me/theorems/5e624be1-77d8-40df-94b3-c311a59a4260
-- title:
--   Proposition 4.1
-- statement:
--   Let $V$ be a Hausdorff real topological vector space and let $C\subseteq V$ be nonempty, closed and convex. Define its recession set by
--   $$
--   \operatorname{lim}(C)=\{v\in V: C+v\subseteq C\}.
--   $$
--   Then the following four assertions hold.
--
--   1. The set $\operatorname{lim}(C)$ is a closed convex cone.
--   2. A vector $v$ belongs to $\operatorname{lim}(C)$ if and only if there are sequences $c_n\in C$ and $t_n\ge0$ with $t_n\to0$ and $t_nc_n\to v$ in the topology of $V$.
--   3. If $c\in C$ and $c+tx\in C$ for every real $t\ge0$, then $x\in\operatorname{lim}(C)$.
--   4. If $C$ is bounded in the topological vector space sense, then $\operatorname{lim}(C)=\{0\}$.
--
--   This describes recession directions without requiring a norm, local convexity, completeness, or a sequential description of the topology.
-- source:
--   A complex semigroup approach to group algebras of infinite dimensional Lie groups, arXiv:0709.1062v1, PDF p. 24, Proposition 4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P13

namespace QAlgorithms.Papers.Independent.Intake100.P13

open Set Filter Topology

noncomputable section

universe u v w

/-- Proposition 4.1, PDF p. 24: all four clauses, including sequence
witnesses and topological boundedness. Local convexity is not assumed.
The translation set is computed in the statement: the accepted recession
constant requires a normed space and cannot express this general TVS case. -/
theorem proposition_4_1
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    (C : Set V) (hC : C.Nonempty) (hClosed : IsClosed C) (hConvex : Convex ℝ C) :
    let R : Set V := {x | ∀ c ∈ C, c + x ∈ C}
    (IsClosed (R) ∧ Convex ℝ (R) ∧
      ∀ (t : ℝ), 0 ≤ t → ∀ x ∈ R, t • x ∈ R) ∧
    R = {x | ∃ (t : ℕ → ℝ) (c : ℕ → V),
      (∀ n, c n ∈ C) ∧ Tendsto t atTop (𝓝 0) ∧ (∀ n, 0 ≤ t n) ∧
        Tendsto (fun n => t n • c n) atTop (𝓝 x)} ∧
    (∀ c ∈ C, ∀ x : V,
      (∀ t : ℝ, 0 ≤ t → c + t • x ∈ C) → x ∈ R) ∧
    (Bornology.IsVonNBounded ℝ C → R = {0}) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P13
