-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SecFiniteUnit_lineSub_aeval_967c21aa8c8f
-- name    : P2M_GroundTheory_Heights__Heights_SecFiniteUnit_lineSub_aeval_967c21aa8c8f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:51:50.556447+00:00
-- url     : https://prove2.me/theorems/bea09f7f-a85f-5f13-aa97-40db9dbb981a
-- title:
--   P2 M Ground Theory Heights  Heights Sec Finite Unit line Sub aeval 967c21aa8c8f: P2 M Ground Theory Heights  Heights Sec Finite Unit line Sub aeval 967c21aa8c8f
-- statement:
--   The P2 M Ground Theory Heights  Heights Sec Finite Unit line Sub aeval 967c21aa8c8f construction uses the P2 M Ground Theory Heights  Heights Sec Finite Unit line Sub aeval 967c21aa8c8f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecFiniteUnit.lean#L65-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecFiniteUnit.lean#L65-L92

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

theorem P2M_GroundTheory_Heights__Heights_SecFiniteUnit_lineSub_aeval_967c21aa8c8f {δ : ℕ} {g : MvPolynomial (Fin (e + 1) × Fin n) k} (hg : IsMultiHomog δ g)
    (y : Par e n → R) (m : Fin n) :
    (aeval (lineSub y m) g).natDegree ≤ δ ∧
      (aeval (lineSub y m) g).coeff δ =
        eval (fun j => y (.inr j)) (specRest (algebraMap k R) g y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SecFiniteUnit».«lineSub_aeval» := P2M_GroundTheory_Heights__Heights_SecFiniteUnit_lineSub_aeval_967c21aa8c8f
