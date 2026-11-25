-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_eq_zero_of_monomial_mul_43714485359b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_eq_zero_of_monomial_mul_43714485359b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:26:41.482562+00:00
-- url     : https://prove2.me/theorems/8db0b98b-23be-4e32-ab6c-cd58822c1b5c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHFree Indep eq zero of monomial mul 43714485359b: P2 M Ground Theory Heights  Heights Kleiman KHFree Indep eq zero of monomial mul 43714485359b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHFree Indep eq zero of monomial mul 43714485359b construction uses the P2 M Ground Theory Heights  Heights Kleiman KHFree Indep eq zero of monomial mul 43714485359b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeIndep.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeIndep.lean#L32-L37

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_eq_zero_of_monomial_mul_43714485359b (e : (Σ k, ι k) →₀ ℕ) {p : MRingOver S ι}
    (h : monomial e (1 : S) * p = 0) : p = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHFreeIndep».«eq_zero_of_monomial_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_eq_zero_of_monomial_mul_43714485359b
