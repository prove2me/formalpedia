-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locEmb_smul__c950eebc53d8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locEmb_smul__c950eebc53d8
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:09:08.855352+00:00
-- url     : https://prove2.me/theorems/98580068-d65c-5bbf-8eba-4bacb12c3f51
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Emb smul  c950eebc53d8: P2 M Ground Theory Heights  Heights Kleiman loc Emb smul  c950eebc53d8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Emb smul  c950eebc53d8 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Emb smul  c950eebc53d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitLoc.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitLoc.lean#L108-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitLoc
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
open MvPolynomial Pointwise AddMonoidAlgebra
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)
variable (M₀ : FinGradedSub (S := S) (x := x) Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locEmb_smul__c950eebc53d8 {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) (c : MvPolynomial (Fin (r + 1)) S)
    (w : LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) I) :
    UT.toL (locEmb η M₀ I hI (c • w)) = yHom S η c * UT.toL (locEmb η M₀ I hI w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locEmb_smul'» := P2M_GroundTheory_Heights__Heights_Kleiman_locEmb_smul__c950eebc53d8
