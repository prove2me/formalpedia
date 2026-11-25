-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_det_funMat_perm
-- name    : ReciprocityTheory.PGsh.det_funMat_perm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:09:33.973941+00:00
-- url     : https://prove2.me/theorems/abd8772f-0383-46da-bcc7-fda844807dc9
-- title:
--   PGsh: det fun Mat perm
-- statement:
--   The PGsh construction uses the det fun Mat perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L250-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L250-L258

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

theorem ReciprocityTheory.PGsh.det_funMat_perm (σ : Equiv.Perm (Fin n)) : (funMat σ).det = Equiv.Perm.sign σ := by sorry
