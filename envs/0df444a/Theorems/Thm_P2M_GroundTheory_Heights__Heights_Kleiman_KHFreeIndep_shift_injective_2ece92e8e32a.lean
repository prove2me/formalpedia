-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_shift_injective_2ece92e8e32a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_shift_injective_2ece92e8e32a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:26:34.546728+00:00
-- url     : https://prove2.me/theorems/6fb22dcc-4084-4a9d-8b51-8b48a0c8452b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHFree Indep shift injective 2ece92e8e32a: P2 M Ground Theory Heights  Heights Kleiman KHFree Indep shift injective 2ece92e8e32a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHFree Indep shift injective 2ece92e8e32a construction uses the P2 M Ground Theory Heights  Heights Kleiman KHFree Indep shift injective 2ece92e8e32a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeIndep.lean#L52-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeIndep.lean#L52-L60

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_shift_injective_2ece92e8e32a (u : (Σ k, ι k) →₀ ℕ) {b b' : (Σ k, ι k) → ℤ} (hb : negExp b ≤ u)
    (hb' : negExp b' ≤ u) (h : posExp b + u - negExp b = posExp b' + u - negExp b') : b = b' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHFreeIndep».«shift_injective» := P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_shift_injective_2ece92e8e32a
