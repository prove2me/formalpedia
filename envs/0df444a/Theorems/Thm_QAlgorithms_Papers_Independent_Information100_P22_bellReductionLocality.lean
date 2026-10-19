-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_bellReductionLocality
-- name    : QAlgorithms.Papers.Independent.Information100.P22.bellReductionLocality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:59:34.665646+00:00
-- url     : https://prove2.me/theorems/ad49529f-ceac-4fa7-b4db-251dfcc39472
-- title:
--   Observation 2: Locality of the Bell reduction
-- statement:
--   Under the preceding ordered-cut and invertibility assumptions, the specified normalizer $U_N$ is a product of single-qubit Cliffords up to a noise-wire permutation exactly when
--   $$A_S=A_N=0,\qquad B\text{ is a binary permutation matrix}.$$
--   Equivalently the graph is a perfect matching across this cut. Arbitrary one-qubit unitary phases are allowed in the factors. The assertion concerns this normalizer, and does not classify other recovery maps.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 11, Observation 2: Locality of the Bell reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Observation 2, PDF p.11, proof pp.36–37: classifies only this canonicalization. -/
theorem bellReductionLocality (nu : ℕ) (hnu : 1 ≤ nu) (G : CutGraph (Fin nu))
    (hB : IsUnit G.B.det) :
    LocalCliffordPermutation (bellNormalizer G) ↔
      G.AS = 0 ∧ G.AN = 0 ∧ BinaryPermutation G.B := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
