-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SecRankSpecialize_secMap_mk_98e321aae280
-- name    : P2M_GroundTheory_Heights__Heights_SecRankSpecialize_secMap_mk_98e321aae280
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:11:09.264083+00:00
-- url     : https://prove2.me/theorems/03db08f0-2a90-4054-bf6d-ca8c0ae32129
-- title:
--   P2 M Ground Theory Heights  Heights Sec Rank Specialize sec Map mk 98e321aae280: P2 M Ground Theory Heights  Heights Sec Rank Specialize sec Map mk 98e321aae280
-- statement:
--   The P2 M Ground Theory Heights  Heights Sec Rank Specialize sec Map mk 98e321aae280 construction uses the P2 M Ground Theory Heights  Heights Sec Rank Specialize sec Map mk 98e321aae280 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecRankSpecialize.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecRankSpecialize.lean#L22-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecRankSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecAlgFieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSecRankSpecialize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SecRankSpecialize
open Vertical

theorem P2M_GroundTheory_Heights__Heights_SecRankSpecialize_secMap_mk_98e321aae280 {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] {n e : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) (p : MvPolynomial (Fin n) R) :
    secMap S Q y (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SecRankSpecialize».«secMap_mk» := P2M_GroundTheory_Heights__Heights_SecRankSpecialize_secMap_mk_98e321aae280
