-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_h1GenAmple_of_subsingleton_920f91cfcb7d
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_h1GenAmple_of_subsingleton_920f91cfcb7d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:14.056472+00:00
-- url     : https://prove2.me/theorems/6e2cab7a-d9c8-4ff0-a19e-d9cc4d4ac044
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel h1 Gen Ample of subsingleton 920f91cfcb7d: P2 M Ground Theory Heights  Heights Hilbert Samuel h1 Gen Ample of subsingleton 920f91cfcb7d
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel h1 Gen Ample of subsingleton 920f91cfcb7d construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel h1 Gen Ample of subsingleton 920f91cfcb7d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/GeneratedModOfSubsingleton.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/GeneratedModOfSubsingleton.lean#L85-L87

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_h1GenAmple_of_subsingleton_920f91cfcb7d (V : Ideal (MRingOver S ι)) (N : K → ℤ) : H1GenAmple S V N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«h1GenAmple_of_subsingleton» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_h1GenAmple_of_subsingleton_920f91cfcb7d
