-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SecFiniteUnit_lineSub_natDegree_le_1289fb635f71
-- name    : P2M_GroundTheory_Heights__Heights_SecFiniteUnit_lineSub_natDegree_le_1289fb635f71
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:54:52.123029+00:00
-- url     : https://prove2.me/theorems/84936b44-487f-4ace-83b3-3a309b295fb8
-- title:
--   P2 M Ground Theory Heights  Heights Sec Finite Unit line Sub nat Degree le 1289fb635f71: P2 M Ground Theory Heights  Heights Sec Finite Unit line Sub nat Degree le 1289fb635f71
-- statement:
--   The P2 M Ground Theory Heights  Heights Sec Finite Unit line Sub nat Degree le 1289fb635f71 construction uses the P2 M Ground Theory Heights  Heights Sec Finite Unit line Sub nat Degree le 1289fb635f71 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecFiniteUnit.lean#L38-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecFiniteUnit.lean#L38-L47

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

theorem P2M_GroundTheory_Heights__Heights_SecFiniteUnit_lineSub_natDegree_le_1289fb635f71 (y : Par e n → R) (m : Fin n) (ij : Fin (e + 1) × Fin n) :
    (lineSub y m ij).natDegree ≤ groupWeight (e + 1) n ij 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SecFiniteUnit».«lineSub_natDegree_le» := P2M_GroundTheory_Heights__Heights_SecFiniteUnit_lineSub_natDegree_le_1289fb635f71
