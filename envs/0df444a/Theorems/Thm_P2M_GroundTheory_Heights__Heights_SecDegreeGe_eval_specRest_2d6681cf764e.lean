-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SecDegreeGe_eval_specRest_2d6681cf764e
-- name    : P2M_GroundTheory_Heights__Heights_SecDegreeGe_eval_specRest_2d6681cf764e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:37:18.878222+00:00
-- url     : https://prove2.me/theorems/0af72cfb-4227-5f5c-ab42-629a08da966c
-- title:
--   P2 M Ground Theory Heights  Heights Sec Degree Ge eval spec Rest 2d6681cf764e: P2 M Ground Theory Heights  Heights Sec Degree Ge eval spec Rest 2d6681cf764e
-- statement:
--   The P2 M Ground Theory Heights  Heights Sec Degree Ge eval spec Rest 2d6681cf764e construction uses the P2 M Ground Theory Heights  Heights Sec Degree Ge eval spec Rest 2d6681cf764e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecDegreeGe.lean#L20-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecDegreeGe.lean#L20-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecDegreeGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecFiniteUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecRankSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowFormHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSecDegreeGe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_eval_specRest_c1d6a2947cb7

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
open GroundTheory.Heights₂.Heights.SecDegreeGe
variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SecDegreeGe_eval_specRest_2d6681cf764e (ψ : k →+* R) (f : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → R) (v : Fin n → R) :
    eval v (Vertical.specRest ψ f y) =
      eval₂ ψ (fun ij => Fin.cases (motive := fun _ => R) (v ij.2)
        (fun i => y (.inl (i, ij.2))) ij.1) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SecDegreeGe».«eval_specRest» := P2M_GroundTheory_Heights__Heights_SecDegreeGe_eval_specRest_2d6681cf764e
