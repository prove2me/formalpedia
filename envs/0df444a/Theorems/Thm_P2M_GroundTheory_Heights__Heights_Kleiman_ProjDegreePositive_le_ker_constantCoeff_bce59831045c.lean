-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_le_ker_constantCoeff_bce59831045c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_le_ker_constantCoeff_bce59831045c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:59:16.969592+00:00
-- url     : https://prove2.me/theorems/dc62de75-6ff5-56e9-967e-9e1b8a14ebcd
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive le ker constant Coeff bce59831045c: P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive le ker constant Coeff bce59831045c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive le ker constant Coeff bce59831045c construction uses the P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive le ker constant Coeff bce59831045c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PProjDegreePositive.lean#L134-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PProjDegreePositive.lean#L134-L147

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegreePos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertDimZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIntersectionRecursion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PProjDegreePositive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.ProjDegreePositive
variable {F : Type u} [Field F] {ι₀ : Type} [Fintype ι₀]
omit [Fintype ι₀]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_le_ker_constantCoeff_bce59831045c (q : Ideal (MRing (fun _ : Unit => ι₀) F)) (hq : IsMultiProjPrime q) :
    q ≤ RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ProjDegreePositive».«le_ker_constantCoeff» := P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_le_ker_constantCoeff_bce59831045c
