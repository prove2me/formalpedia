-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_twoQubitProductVector
-- name    : QAlgorithms.Papers.Independent.Information100.P21.twoQubitProductVector
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:46:21.879815+00:00
-- url     : https://prove2.me/theorems/41d501e9-3317-4db5-bd3b-ed27e13831b0
-- title:
--   II.2 — Lemma II.2 (Two-qubit product-vector lemma). Every subspace V ⊂ C2 ⊗ C2 with dim V ≥ 2 contains a nonzero
-- statement:
--   Let $V\subseteq\mathbb C^2\otimes\mathbb C^2$ be a complex subspace with $\dim V\ge2$. Then
--   $$\exists e,f\quad 0\ne e\otimes f\in V.$$
--   The nonzero qualification excludes the trivial zero product. The source includes a proof and credits Refs. [13,14].
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 6, II.2 — Lemma II.2 (Two-qubit product-vector lemma). Every subspace V ⊂ C2 ⊗ C2 with dim V ≥ 2 contains a nonzero

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 6, Lemma II.2 (Two-qubit product-vector lemma). Every subspace V ⊂ C2 ⊗ C2 with dim V ≥ 2 contains a nonzero. -/
theorem twoQubitProductVector (V : Submodule ℂ (Vec QQ)) (h : 2 ≤ Module.finrank ℂ V) :
  ∃ e f : Vec (Fin 2), tensor e f ∈ V ∧ tensor e f ≠ 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
