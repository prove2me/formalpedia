-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_chowForm_vanish_aa54c6828c1b
-- name    : P2M_GroundTheory_Heights__Heights_PointLine_chowForm_vanish_aa54c6828c1b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:14:53.472809+00:00
-- url     : https://prove2.me/theorems/f1a1d332-48dc-4378-87f4-5c2ce6cb782a
-- title:
--   P2 M Ground Theory Heights  Heights Point Line chow Form vanish aa54c6828c1b: P2 M Ground Theory Heights  Heights Point Line chow Form vanish aa54c6828c1b
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Line chow Form vanish aa54c6828c1b construction uses the P2 M Ground Theory Heights  Heights Point Line chow Form vanish aa54c6828c1b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPointLine.lean#L109-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPointLine.lean#L109-L131

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
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
open GroundTheory.Heights₂.Heights.PointLine
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PointLine_chowForm_vanish_aa54c6828c1b {W : Ideal (MvPolynomial (Fin n) ℂ)} {g : MvPolynomial (Fin 1 × Fin n) ℂ}
    (hg : IsChowForm W 1 g) {y : Fin n → ℂ} (hy0 : y ≠ 0) (hy : ∀ q ∈ W, eval y q = 0)
    (u : Fin 1 × Fin n → ℂ) (hu : eval u (pairing y) = 0) : eval u g = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointLine».«chowForm_vanish» := P2M_GroundTheory_Heights__Heights_PointLine_chowForm_vanish_aa54c6828c1b
