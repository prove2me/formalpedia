-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_cechHc_one_subsingleton_0d6516e3ebc0
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_cechHc_one_subsingleton_0d6516e3ebc0
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:22.184083+00:00
-- url     : https://prove2.me/theorems/dd26a24d-35ff-4679-976c-0a444a77c067
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel cech Hc one subsingleton 0d6516e3ebc0: P2 M Ground Theory Heights  Heights Hilbert Samuel cech Hc one subsingleton 0d6516e3ebc0
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel cech Hc one subsingleton 0d6516e3ebc0 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel cech Hc one subsingleton 0d6516e3ebc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/GeneratedModOfSubsingleton.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/GeneratedModOfSubsingleton.lean#L46-L54

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_cechHc_one_subsingleton_0d6516e3ebc0 {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) :
    Subsingleton (KH.cechHc ι 𝓜 d 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«cechHc_one_subsingleton» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_cechHc_one_subsingleton_0d6516e3ebc0
