-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_h1_vanish_generated_of_localized_subsingleton_ba7e604619d4
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_h1_vanish_generated_of_localized_subsingleton_ba7e604619d4
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:49.405479+00:00
-- url     : https://prove2.me/theorems/c760a97b-6b24-4f7a-a705-6f712bad8087
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel h1 vanish generated of localized subsingleton ba7e604619d4: P2 M Ground Theory Heights  Heights Hilbert Samuel h1 vanish generated of localized subsi
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel h1 vanish generated of localized subsingleton ba7e604619d4 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel h1 vanish generated of localized subsingleton ba7e604619d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/H1VanishGeneratedOfLocalizedSubsingleton.lean#L36-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/H1VanishGeneratedOfLocalizedSubsingleton.lean#L36-L48

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_h1_vanish_generated_of_localized_subsingleton_ba7e604619d4
    (h : ∀ (n : ℕ) (I : KH.Cell K ι n), Subsingleton (LocalizedModule (KH.cellMon S I.1) M))
    (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) :
    Subsingleton (KH.cechHc ι 𝓜 d 1) ∧ GeneratedMod S ι 𝓜 d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«h1_vanish_generated_of_localized_subsingleton» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_h1_vanish_generated_of_localized_subsingleton_ba7e604619d4
