-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_tanLinPoly_smul_6210bcafaeca
-- name    : P2M_GroundTheory_Heights__Heights_tanLinPoly_smul_6210bcafaeca
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:50:29.599492+00:00
-- url     : https://prove2.me/theorems/2d999429-4445-4076-b2ea-aff3afc1d02c
-- title:
--   P2 M Ground Theory Heights  Heights tan Lin Poly smul 6210bcafaeca: P2 M Ground Theory Heights  Heights tan Lin Poly smul 6210bcafaeca
-- statement:
--   The P2 M Ground Theory Heights  Heights tan Lin Poly smul 6210bcafaeca construction uses the P2 M Ground Theory Heights  Heights tan Lin Poly smul 6210bcafaeca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L55-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff
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
open MvPolynomial Module
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_tanLinPoly_smul_6210bcafaeca (p w : Fin n → ℂ) (c : ℂ) : tanLinPoly p (c • w) = C c * tanLinPoly p w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«tanLinPoly_smul» := P2M_GroundTheory_Heights__Heights_tanLinPoly_smul_6210bcafaeca
