-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_det_ne_of_span
-- name    : ReciprocityTheory.PGsh.Up.det_ne_of_span
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T18:29:23.066154+00:00
-- url     : https://prove2.me/theorems/4f6fd2cb-9bd4-4f0e-8550-a42744951d2b
-- title:
--   Up: det ne of span
-- statement:
--   The Up construction uses the det ne of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UpBrChar.lean#L25-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UpBrChar.lean#L25-L42

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

theorem ReciprocityTheory.PGsh.Up.det_ne_of_span {s : ℕ} (A : Matrix (Fin s) (Fin s) R) (c : R) (hc : c ≠ 0)
    (h : ∀ w : Fin s → R, c • w ∈ Submodule.span R (Set.range fun i => fun a => A a i)) :
    A.det ≠ 0 := by sorry
