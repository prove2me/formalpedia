-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_monoList_perm_282dba544287
-- name    : P2M_GroundTheory_Heights__Heights_FlagTypings_monoList_perm_282dba544287
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:03.633237+00:00
-- url     : https://prove2.me/theorems/d791197d-ee85-466c-b02f-0894004f17e1
-- title:
--   P2 M Ground Theory Heights  Heights Flag Typings mono List perm 282dba544287: P2 M Ground Theory Heights  Heights Flag Typings mono List perm 282dba544287
-- statement:
--   The P2 M Ground Theory Heights  Heights Flag Typings mono List perm 282dba544287 construction uses the P2 M Ground Theory Heights  Heights Flag Typings mono List perm 282dba544287 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L170-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L170-L173

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FlagTypings
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_FlagTypings_monoList_perm_282dba544287 {N : ℕ} (cls : Fin N → K → ℤ) (μ : Fin N →₀ ℕ) :
    ((IndefiniteRowSideFullHecke.NumbersDVR.monoList μ).map cls).Perm (NumbersDVR.classList cls μ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FlagTypings».«monoList_perm» := P2M_GroundTheory_Heights__Heights_FlagTypings_monoList_perm_282dba544287
