-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMGraded_punit_4e0d05a18e96
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMGraded_punit_4e0d05a18e96
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:08.845832+00:00
-- url     : https://prove2.me/theorems/13c1ee6e-fa4d-5f44-bcb5-bce98d37b31b
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel is MGraded punit 4e0d05a18e96: P2 M Ground Theory Heights  Heights Hilbert Samuel is MGraded punit 4e0d05a18e96
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel is MGraded punit 4e0d05a18e96 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel is MGraded punit 4e0d05a18e96 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/H1VanishGeneratedOfLocalizedSubsingleton.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/H1VanishGeneratedOfLocalizedSubsingleton.lean#L52-L54

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
omit [LinearOrder K] [∀ k, LinearOrder (ι k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMGraded_punit_4e0d05a18e96 : KH.IsMGraded S ι (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«isMGraded_punit» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMGraded_punit_4e0d05a18e96
