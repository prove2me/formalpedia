-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_pow_eq_twistMul_twist_a9905eaca05a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twist_pow_eq_twistMul_twist_a9905eaca05a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:05:18.950919+00:00
-- url     : https://prove2.me/theorems/6fa823e5-feed-5396-8f33-cc3544794623
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist pow eq twist Mul twist a9905eaca05a: P2 M Ground Theory Heights  Heights Kleiman twist pow eq twist Mul twist a9905eaca05a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist pow eq twist Mul twist a9905eaca05a construction uses the P2 M Ground Theory Heights  Heights Kleiman twist pow eq twist Mul twist a9905eaca05a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L96-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L96-L108

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
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
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twist_pow_eq_twistMul_twist_a9905eaca05a (M H T : SubSystem k x Ω)
    (hT : ∀ I, T.sub I = twistMod k x (-1) I) (q c m : ℕ) :
    (M.pow q).twist (H.pow (c * m)) =
      (twistMul M q (m : ℤ)).twist ((T.twist (H.pow c)).pow m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twist_pow_eq_twistMul_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_twist_pow_eq_twistMul_twist_a9905eaca05a
