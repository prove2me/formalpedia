-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SecDegreeGe_map_eval_specRest_c1db2bdd1d7e
-- name    : P2M_GroundTheory_Heights__Heights_SecDegreeGe_map_eval_specRest_c1db2bdd1d7e
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:32:53.662572+00:00
-- url     : https://prove2.me/theorems/093bca0b-1f26-53be-a41e-b265a4dd478a
-- title:
--   P2 M Ground Theory Heights  Heights Sec Degree Ge map eval spec Rest c1db2bdd1d7e: P2 M Ground Theory Heights  Heights Sec Degree Ge map eval spec Rest c1db2bdd1d7e
-- statement:
--   The P2 M Ground Theory Heights  Heights Sec Degree Ge map eval spec Rest c1db2bdd1d7e construction uses the P2 M Ground Theory Heights  Heights Sec Degree Ge map eval spec Rest c1db2bdd1d7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecDegreeGe.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecDegreeGe.lean#L35-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecDegreeGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecFiniteUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecRankSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowFormHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSecDegreeGe
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

theorem P2M_GroundTheory_Heights__Heights_SecDegreeGe_map_eval_specRest_c1db2bdd1d7e (ψ : k →+* R) (φ : R →+* S) (f : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → R) :
    φ (eval (fun j => y (.inr j)) (Vertical.specRest ψ f y)) =
      eval (fun j => φ (y (.inr j))) (Vertical.specRest (φ.comp ψ) f (φ ∘ y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SecDegreeGe».«map_eval_specRest» := P2M_GroundTheory_Heights__Heights_SecDegreeGe_map_eval_specRest_c1db2bdd1d7e
