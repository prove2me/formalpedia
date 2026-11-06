-- Prove2me | Theorems.Thm_QEC_Locality_semanticStabilizerDistance_localPauli_pairProductCriterion
-- name    : QEC.Locality.semanticStabilizerDistance_localPauli_pairProductCriterion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:30:45.594993+00:00
-- url     : https://prove2.me/theorems/b17fe061-e3c7-4a92-b21b-7f220e93d1df
-- title:
--   Locality: semantic Stabilizer Distance local Pauli pair Product Criterion
-- statement:
--   Semantic stabilizer-distance leastness gives the exact M3 pair-product
--   disjunction for every pair of local twirl branches below the selected size.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/SemanticDistanceErasure.lean#L347-L373
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/SemanticDistanceErasure.lean#L347-L373

import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Locality
open QEC Semantics Coding
open scoped TensorProduct
open PauliSymplectic
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.semanticStabilizerDistance_localPauli_pairProductCriterion
    (Q : StabilizerCode.SourceValidBinary ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q d)
    (S : FiniteSubsystem ι) (hSelected : S.selected.card < d) :
    ∀ p q : LocalPauliWordIndex S,
      Q.1.InGeneratedGroupUpToSign
          (binaryMul (binaryDagger (embeddedLocalPauli S p))
            (embeddedLocalPauli S q)) ∨
        ¬ Q.1.InBinaryNormalizer
          (binaryMul (binaryDagger (embeddedLocalPauli S p))
            (embeddedLocalPauli S q)) := by sorry
