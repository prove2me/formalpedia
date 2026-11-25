-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SecFiniteUnit_coord_integral_6856479499b7
-- name    : P2M_GroundTheory_Heights__Heights_SecFiniteUnit_coord_integral_6856479499b7
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:04:27.289947+00:00
-- url     : https://prove2.me/theorems/323fc0f8-3999-5632-859a-37e0933c22ca
-- title:
--   P2 M Ground Theory Heights  Heights Sec Finite Unit coord integral 6856479499b7: P2 M Ground Theory Heights  Heights Sec Finite Unit coord integral 6856479499b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Sec Finite Unit coord integral 6856479499b7 construction uses the P2 M Ground Theory Heights  Heights Sec Finite Unit coord integral 6856479499b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecFiniteUnit.lean#L94-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecFiniteUnit.lean#L94-L177

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecFiniteUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_AssemblyPartial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSecFiniteUnit
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
open MvPolynomial Vertical
noncomputable section
open GroundTheory.Heights₂.Heights.SecFiniteUnit
variable {k R : Type} [Field k] [CommRing R] [Algebra k R] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SecFiniteUnit_coord_integral_6856479499b7 {δ : ℕ} (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k) (y : Par e n → R)
    (hg : IsChowForm Q (e + 1) g) (hδ : IsMultiHomog δ g)
    (hu : IsUnit (eval (fun j => y (.inr j)) (specRest (algebraMap k R) g y))) (m : Fin n) :
    IsIntegral R (secCoord (Q.map (MvPolynomial.map (algebraMap k R))) y m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SecFiniteUnit».«coord_integral» := P2M_GroundTheory_Heights__Heights_SecFiniteUnit_coord_integral_6856479499b7
