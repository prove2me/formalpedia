-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locEmb_injective_984fd01350e8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locEmb_injective_984fd01350e8
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:34:29.125435+00:00
-- url     : https://prove2.me/theorems/2c8e503e-0312-5892-9e36-7b350e0ab259
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Emb injective 984fd01350e8: P2 M Ground Theory Heights  Heights Kleiman loc Emb injective 984fd01350e8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Emb injective 984fd01350e8 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Emb injective 984fd01350e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitLoc.lean#L114-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitLoc.lean#L114-L124

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locEmb_injective_984fd01350e8 {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) :
    Function.Injective (locEmb η M₀ I hI) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locEmb_injective» := P2M_GroundTheory_Heights__Heights_Kleiman_locEmb_injective_984fd01350e8
