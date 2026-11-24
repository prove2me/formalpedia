-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMultiHomog_one_zero_4334cb17c577
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMultiHomog_one_zero_4334cb17c577
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:30.397988+00:00
-- url     : https://prove2.me/theorems/5fe87f5a-92f4-4f1e-bb2d-5553d2a2fadc
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel is Multi Homog one zero 4334cb17c577: P2 M Ground Theory Heights  Heights Hilbert Samuel is Multi Homog one zero 4334cb17c577
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel is Multi Homog one zero 4334cb17c577 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel is Multi Homog one zero 4334cb17c577 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/GeneratedModOfSubsingleton.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/GeneratedModOfSubsingleton.lean#L58-L66

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
omit [Fintype K] [∀ k, Subsingleton (ι k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMultiHomog_one_zero_4334cb17c577 : IsMultiHomog (1 : MRingOver S ι) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«isMultiHomog_one_zero» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMultiHomog_one_zero_4334cb17c577
