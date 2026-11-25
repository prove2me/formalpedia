-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_cellMon_monomial_80cf923a0fe8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_cellMon_monomial_80cf923a0fe8
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:26:43.559843+00:00
-- url     : https://prove2.me/theorems/6445be37-7eac-4d39-8313-93c6a26769f0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp cell Mon monomial 80cf923a0fe8: P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp cell Mon monomial 80cf923a0fe8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp cell Mon monomial 80cf923a0fe8 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp cell Mon monomial 80cf923a0fe8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeDecomp.lean#L15-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeDecomp.lean#L15-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeDecompSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHFreeDecomp
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
open GroundTheory.Heights₂.Heights.Kleiman.KHFreeDecomp
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_cellMon_monomial_80cf923a0fe8 {I : ∀ k, Finset (ι k)} {t : MRingOver S ι} (ht : t ∈ KH.cellMon S I) :
    ∃ u : (Σ k, ι k) →₀ ℕ, t = monomial u 1 ∧ ∀ q ∈ u.support, q.2 ∈ I q.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHFreeDecomp».«cellMon_monomial» := P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_cellMon_monomial_80cf923a0fe8
