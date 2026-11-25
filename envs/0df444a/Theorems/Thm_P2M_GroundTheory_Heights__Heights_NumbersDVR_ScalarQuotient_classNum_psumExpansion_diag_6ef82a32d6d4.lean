-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_psumExpansion_diag_6ef82a32d6d4
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_psumExpansion_diag_6ef82a32d6d4
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:07:56.907383+00:00
-- url     : https://prove2.me/theorems/d684cdba-4254-4b68-b3c9-ecb8e482f097
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class Num psum Expansion diag 6ef82a32d6d4: P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class Num psum Expansion dia
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class Num psum Expansion diag 6ef82a32d6d4 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient class Num psum Expansion diag 6ef82a32d6d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L68-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L68-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PScalarQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_psumExpansion_diag_6ef82a32d6d4 {N : ℕ} (x : Fin N → K → ℤ) (k : ℕ) (i : Fin N)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum (Sum.elim x x) (psumExpansion N k i) Q W =
      k * vNumL W (classList x (Finsupp.single i (k - 1)) ++ Q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ScalarQuotient».«classNum_psumExpansion_diag» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_psumExpansion_diag_6ef82a32d6d4
