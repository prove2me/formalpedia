-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_cellMon_monomial_bdac4391f48a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_cellMon_monomial_bdac4391f48a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:36:15.319189+00:00
-- url     : https://prove2.me/theorems/83d96b8b-4016-5af2-ad83-58e2dcd482bd
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHFree Indep cell Mon monomial bdac4391f48a: P2 M Ground Theory Heights  Heights Kleiman KHFree Indep cell Mon monomial bdac4391f48a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHFree Indep cell Mon monomial bdac4391f48a construction uses the P2 M Ground Theory Heights  Heights Kleiman KHFree Indep cell Mon monomial bdac4391f48a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeIndep.lean#L17-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeIndep.lean#L17-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeIndepSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHFreeIndep
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
open GroundTheory.Heights₂.Heights.Kleiman.KHFreeIndep
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_cellMon_monomial_bdac4391f48a {I : ∀ k, Finset (ι k)} {t : MRingOver S ι} (ht : t ∈ KH.cellMon S I) :
    ∃ e, t = monomial e 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHFreeIndep».«cellMon_monomial» := P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_cellMon_monomial_bdac4391f48a
