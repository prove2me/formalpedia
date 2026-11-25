-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_cayDet_map
-- name    : ReciprocityTheory.PGsh.cayDet_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:31:31.791047+00:00
-- url     : https://prove2.me/theorems/14142469-c324-453c-ba5a-8ef027e0300b
-- title:
--   PGsh: cay Det map
-- statement:
--   The PGsh construction uses the cay Det map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L457-L463
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L457-L463

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}
variable {R : Type*} [CommRing R]

theorem ReciprocityTheory.PGsh.cayDet_map : map (Int.castRingHom R) (cayDet n ℤ) = cayDet n R := by sorry
