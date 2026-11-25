-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_TranslateEq_sPow_eq_monoSec_dddd22f75433
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_TranslateEq_sPow_eq_monoSec_dddd22f75433
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:46:59.753496+00:00
-- url     : https://prove2.me/theorems/a8b817a7-1604-426c-a640-40564c1d0f5e
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Translate Eq s Pow eq mono Sec dddd22f75433: P2 M Ground Theory Heights  Heights Effective HS Translate Eq s Pow eq mono Sec dddd22f75433
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Translate Eq s Pow eq mono Sec dddd22f75433 construction uses the P2 M Ground Theory Heights  Heights Effective HS Translate Eq s Pow eq mono Sec dddd22f75433 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/MemSectionsOfHolLineBundleEquiv.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/MemSectionsOfHolLineBundleEquiv.lean#L73-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_MemSectionsOfHolLineBundleEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.EffectiveHS
open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.EffectiveHS (topForms topFormWeightedL2 twist wAdd fsPhi HermSpace FSData HSData
  secMul l2n tuples jacDet)
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.EffectiveHS.TranslateEq
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
variable {Y : Type} [TopologicalSpace Y] (d : FSData A Y)

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_TranslateEq_sPow_eq_monoSec_dddd22f75433 (s : Fin D → Fin d.W.n → ℂ) (α : Fin D → ℕ) :
    sPow (fun i => d.W.sec (s i)) α = d.monoSec s α := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«TranslateEq».«sPow_eq_monoSec» := P2M_GroundTheory_Heights__Heights_EffectiveHS_TranslateEq_sPow_eq_monoSec_dddd22f75433
