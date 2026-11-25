-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SecFiniteUnit_weight_sum_24ed28467351
-- name    : P2M_GroundTheory_Heights__Heights_SecFiniteUnit_weight_sum_24ed28467351
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:56:23.562492+00:00
-- url     : https://prove2.me/theorems/49f9d7e7-7122-5bd2-a039-6115862b51fb
-- title:
--   P2 M Ground Theory Heights  Heights Sec Finite Unit weight sum 24ed28467351: P2 M Ground Theory Heights  Heights Sec Finite Unit weight sum 24ed28467351
-- statement:
--   The P2 M Ground Theory Heights  Heights Sec Finite Unit weight sum 24ed28467351 construction uses the P2 M Ground Theory Heights  Heights Sec Finite Unit weight sum 24ed28467351 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecFiniteUnit.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecFiniteUnit.lean#L58-L63

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

theorem P2M_GroundTheory_Heights__Heights_SecFiniteUnit_weight_sum_24ed28467351 {δ : ℕ} {g : MvPolynomial (Fin (e + 1) × Fin n) k} (hg : IsMultiHomog δ g)
    {d : Fin (e + 1) × Fin n →₀ ℕ} (hd : coeff d g ≠ 0) :
    ∑ ij, d ij * groupWeight (e + 1) n ij 0 = δ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SecFiniteUnit».«weight_sum» := P2M_GroundTheory_Heights__Heights_SecFiniteUnit_weight_sum_24ed28467351
