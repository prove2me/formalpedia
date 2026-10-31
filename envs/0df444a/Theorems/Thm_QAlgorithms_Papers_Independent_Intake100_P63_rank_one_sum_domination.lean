-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_rank_one_sum_domination
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.rank_one_sum_domination
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:27:12.602075+00:00
-- url     : https://prove2.me/theorems/fc37a484-318e-4ad9-82a8-5e2a2b5ccfee
-- title:
--   Lemma C.6: rank-one sum domination
-- statement:
--   Let $H$ be a nonzero finite-dimensional complex Hilbert space, let $X$ be any finite index set, and let $\psi_k\in H$ be arbitrary vectors, without normalization requirements. For the specified sum $\Psi=\sum_{k\in X}\psi_k$,
--   $$
--   |\Psi\rangle\langle\Psi|\le |X|\sum_{k\in X}|\psi_k\rangle\langle\psi_k|.
--   $$
--
--   The empty index set gives the zero-operator inequality. The result applies to unnormalized expansion terms.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 33, Lemma C.6: rank-one sum domination

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P63

open QAlgorithms Filter Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat relativeBits)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Advance50.P30 (joinCopies defectTensor)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.33 Lemma C.6 Eq.(C14): the vectors and their sum may be unnormalized.
The empty index set gives precisely the zero-operator inequality. -/
theorem rank_one_sum_domination {I K : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype K] (v : K → Vec I) :
    ((Fintype.card K : ℂ) • (∑ k, pureDensity (v k)) - pureDensity (∑ k, v k)).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
