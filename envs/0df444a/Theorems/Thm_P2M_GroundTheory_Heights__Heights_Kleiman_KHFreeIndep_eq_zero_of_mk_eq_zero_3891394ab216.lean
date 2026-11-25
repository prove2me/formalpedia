-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_eq_zero_of_mk_eq_zero_3891394ab216
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_eq_zero_of_mk_eq_zero_3891394ab216
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:07.005631+00:00
-- url     : https://prove2.me/theorems/70e37057-c095-4b29-82fb-307314287827
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHFree Indep eq zero of mk eq zero 3891394ab216: P2 M Ground Theory Heights  Heights Kleiman KHFree Indep eq zero of mk eq zero 3891394ab216
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHFree Indep eq zero of mk eq zero 3891394ab216 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHFree Indep eq zero of mk eq zero 3891394ab216 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeIndep.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeIndep.lean#L41-L50

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_eq_zero_of_mk_eq_zero_3891394ab216 {I : ∀ k, Finset (ι k)} {p : MRingOver S ι}
    (h : LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) p) (1 : KH.cellMon S I) = 0) :
    p = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHFreeIndep».«eq_zero_of_mk_eq_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_eq_zero_of_mk_eq_zero_3891394ab216
