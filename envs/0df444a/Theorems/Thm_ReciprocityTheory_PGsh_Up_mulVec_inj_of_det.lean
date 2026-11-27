-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_mulVec_inj_of_det
-- name    : ReciprocityTheory.PGsh.Up.mulVec_inj_of_det
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T18:30:38.540453+00:00
-- url     : https://prove2.me/theorems/15b40d03-bf95-44c8-88b6-00df3dceec45
-- title:
--   Up: mul Vec inj of det
-- statement:
--   The Up construction uses the mul Vec inj of det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UpBrChar.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UpBrChar.lean#L62-L67

import Definitions.Def_ReciprocityTheory_DualLattices_DetIntegralNonneg
import Definitions.Def_ReciprocityTheory_DualLattices_UpBrChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R] [IsDomain R]

theorem ReciprocityTheory.PGsh.Up.mulVec_inj_of_det {s : ℕ} (A : Matrix (Fin s) (Fin s) R) (hA : A.det ≠ 0) {x y : Fin s → R}
    (h : A *ᵥ x = A *ᵥ y) : x = y := by sorry
