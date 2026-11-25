-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_loc_subsingleton_of_kill_b025ae05f975
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_loc_subsingleton_of_kill_b025ae05f975
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:57.402667+00:00
-- url     : https://prove2.me/theorems/33372f52-7cb3-4d11-ab41-f46c67d22256
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel loc subsingleton of kill b025ae05f975: P2 M Ground Theory Heights  Heights Hilbert Samuel loc subsingleton of kill b025ae05f975
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel loc subsingleton of kill b025ae05f975 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel loc subsingleton of kill b025ae05f975 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/H1VanishGeneratedOfLocalizedSubsingleton.lean#L24-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/H1VanishGeneratedOfLocalizedSubsingleton.lean#L24-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ImportsSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGradedSubquot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGenSESStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgFiltSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgCechSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_H1VanishGeneratedOfLocalizedSubsingleton
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
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
omit [Fintype K] [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [Module S M]
  [IsScalarTower S (MRingOver S ι) M]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_loc_subsingleton_of_kill_b025ae05f975 {T : Submonoid (MRingOver S ι)} {u : MRingOver S ι} (hu : u ∈ T)
    (hk : ∀ y : M, u • y = 0) : Subsingleton (LocalizedModule T M) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«loc_subsingleton_of_kill» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_loc_subsingleton_of_kill_b025ae05f975
