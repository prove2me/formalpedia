-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_fact22
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.fact22
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:05:46.893961+00:00
-- url     : https://prove2.me/theorems/45767269-5b7f-4657-aac6-38136c5d8960
-- title:
--   Fact 22: partial trace preserves the smaller permutation algebra
-- statement:
--   Let $d\ge2$ be the local dimension, $N\ge2$ the number of ports, and $n=N+1$. All physical diagrams have height at most $d$. Write $m_\lambda$ for its multiplicity in the natural tensor permutation action, $d_\lambda$ for its Specht dimension, and $P_\lambda$ for the full isotypic projector. The relation $\mu\in\alpha$ means adding one box. Let $\mathcal A_n^{t_n}(d)$ be the linear span of the actual partially transposed tensor permutation matrices, and let $\mathbb C[V(S_N)]$ be the represented smaller permutation span. Then
--
--   $$X\in\mathcal A_n^{t_n}(d)\implies\operatorname{Tr}_nX\in\mathbb C[V(S_N)].$$
--
--   This conclusion permits linear dependence among represented permutations; it is not an assertion about an abstract faithful group algebra.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 22, Fact 22: partial trace preserves the smaller permutation algebra

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P33

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted type constructors; local notation only reorders Word's arguments.

local notation "Word" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P58.Word r d)

local notation "Op" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P21.Op
    (QAlgorithms.Papers.Independent.Information100.P58.Word r d))

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

/-- PDF p.22 Fact22: membership in the represented smaller permutation algebra;
no faithfulness of the group algebra is assumed. -/
theorem fact22 (d k : ℕ) (hd : 2 ≤ d) (A : Op d (k+3))
    (hA : A ∈ transposedSpan d (k+2)) :
    traceFinalQudits 1 A ∈ permutationSpan d (k+2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
