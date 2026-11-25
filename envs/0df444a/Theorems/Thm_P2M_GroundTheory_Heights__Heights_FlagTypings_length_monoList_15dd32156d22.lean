-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_length_monoList_15dd32156d22
-- name    : P2M_GroundTheory_Heights__Heights_FlagTypings_length_monoList_15dd32156d22
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:04.341574+00:00
-- url     : https://prove2.me/theorems/5a111471-002f-4edd-b397-2f90479cf316
-- title:
--   P2 M Ground Theory Heights  Heights Flag Typings length mono List 15dd32156d22: P2 M Ground Theory Heights  Heights Flag Typings length mono List 15dd32156d22
-- statement:
--   The P2 M Ground Theory Heights  Heights Flag Typings length mono List 15dd32156d22 construction uses the P2 M Ground Theory Heights  Heights Flag Typings length mono List 15dd32156d22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L176-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L176-L183

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
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FlagTypings_length_monoList_15dd32156d22 {N : ℕ} {Q : MvPolynomial (Fin N) ℤ} {d : ℕ} (hQ : Q.IsHomogeneous d)
    {μ : Fin N →₀ ℕ} (hμ : μ ∈ Q.support) : (IndefiniteRowSideFullHecke.NumbersDVR.monoList μ).length = d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FlagTypings».«length_monoList» := P2M_GroundTheory_Heights__Heights_FlagTypings_length_monoList_15dd32156d22
