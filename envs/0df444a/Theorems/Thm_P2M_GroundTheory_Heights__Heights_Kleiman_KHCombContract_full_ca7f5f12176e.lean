-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_full_ca7f5f12176e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_full_ca7f5f12176e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:29:03.892935+00:00
-- url     : https://prove2.me/theorems/76430b07-92c2-5782-b13d-f9b95cb2d3e7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract full ca7f5f12176e: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract full ca7f5f12176e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract full ca7f5f12176e construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract full ca7f5f12176e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L446-L471
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L446-L471

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombContract
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_full_ca7f5f12176e : KHCombContract.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«full» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_full_ca7f5f12176e
