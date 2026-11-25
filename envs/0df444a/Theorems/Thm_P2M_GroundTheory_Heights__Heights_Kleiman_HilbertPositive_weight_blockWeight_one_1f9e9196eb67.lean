-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPositive_weight_blockWeight_one_1f9e9196eb67
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPositive_weight_blockWeight_one_1f9e9196eb67
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:42:35.307556+00:00
-- url     : https://prove2.me/theorems/8ff6453e-a361-47e5-96b0-a5ada4ab0b72
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Hilbert Positive weight block Weight one 1f9e9196eb67: P2 M Ground Theory Heights  Heights Kleiman Hilbert Positive weight block Weight one 1f9e9196eb67
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Hilbert Positive weight block Weight one 1f9e9196eb67 construction uses the P2 M Ground Theory Heights  Heights Kleiman Hilbert Positive weight block Weight one 1f9e9196eb67 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPositive.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPositive.lean#L49-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegreePos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertDimZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertIncrement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIntersectionRecursion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedHilbertPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PModulesFromPrimes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiltrationHilbSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRankOfSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPositive
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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.HilbertPositive
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPositive_weight_blockWeight_one_1f9e9196eb67 (d : (Σ _ : Unit, Fin (N + 1)) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) d = fun _ => d.degree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«HilbertPositive».«weight_blockWeight_one» := P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPositive_weight_blockWeight_one_1f9e9196eb67
