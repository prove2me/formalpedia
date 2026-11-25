-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_generatedMod_of_subsingleton_6bce206c756e
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_generatedMod_of_subsingleton_6bce206c756e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:37.755802+00:00
-- url     : https://prove2.me/theorems/40e4fa63-92d7-4ede-bd41-47f5cd5a8f24
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel generated Mod of subsingleton 6bce206c756e: P2 M Ground Theory Heights  Heights Hilbert Samuel generated Mod of subsingleton 6bce206c756e
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel generated Mod of subsingleton 6bce206c756e construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel generated Mod of subsingleton 6bce206c756e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/GeneratedModOfSubsingleton.lean#L68-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/GeneratedModOfSubsingleton.lean#L68-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsKleimanScheme
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GeneratedModOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [∀ k, Subsingleton (ι k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_generatedMod_of_subsingleton_6bce206c756e {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) :
    GeneratedMod S ι 𝓜 d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«generatedMod_of_subsingleton» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_generatedMod_of_subsingleton_6bce206c756e
