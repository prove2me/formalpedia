-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SecFiniteUnit_lineSub_coeff_4e9a91de44a9
-- name    : P2M_GroundTheory_Heights__Heights_SecFiniteUnit_lineSub_coeff_4e9a91de44a9
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:52:13.569721+00:00
-- url     : https://prove2.me/theorems/96f63a18-8249-55c8-8e73-595f36aa1cb1
-- title:
--   P2 M Ground Theory Heights  Heights Sec Finite Unit line Sub coeff 4e9a91de44a9: P2 M Ground Theory Heights  Heights Sec Finite Unit line Sub coeff 4e9a91de44a9
-- statement:
--   The P2 M Ground Theory Heights  Heights Sec Finite Unit line Sub coeff 4e9a91de44a9 construction uses the P2 M Ground Theory Heights  Heights Sec Finite Unit line Sub coeff 4e9a91de44a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecFiniteUnit.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecFiniteUnit.lean#L49-L56

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

theorem P2M_GroundTheory_Heights__Heights_SecFiniteUnit_lineSub_coeff_4e9a91de44a9 (y : Par e n → R) (m : Fin n) (ij : Fin (e + 1) × Fin n) :
    (lineSub y m ij).coeff (groupWeight (e + 1) n ij 0) = lineTop y ij := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SecFiniteUnit».«lineSub_coeff» := P2M_GroundTheory_Heights__Heights_SecFiniteUnit_lineSub_coeff_4e9a91de44a9
