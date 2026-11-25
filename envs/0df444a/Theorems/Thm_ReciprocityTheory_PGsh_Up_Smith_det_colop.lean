-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_det_colop
-- name    : ReciprocityTheory.PGsh.Up.Smith.det_colop
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:07:17.777011+00:00
-- url     : https://prove2.me/theorems/0582a413-6619-43c3-b313-f02d1abea6f8
-- title:
--   Smith: det colop
-- statement:
--   The Smith construction uses the det colop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UpSmith.lean#L167-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UpSmith.lean#L167-L192

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.Smith
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.Up.Smith.det_colop {b : ℕ} (X : Matrix (Fin (b + 1)) (Fin (b + 1)) R) (j0 : Fin (b + 1))
    (s : Fin (b + 1) → R) :
    (Matrix.of fun i j => if j = j0 then X i j0 else X i j - s j * X i j0).det = X.det := by sorry
