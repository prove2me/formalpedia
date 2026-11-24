-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_rowSubst_mul
-- name    : ReciprocityTheory.PGsh.rowSubst_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:16:04.001811+00:00
-- url     : https://prove2.me/theorems/f55bddbf-cb11-4f18-baee-e2177526fc56
-- title:
--   PGsh: row Subst mul
-- statement:
--   The PGsh construction uses the row Subst mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FischerSelfNeZero.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FischerSelfNeZero.lean#L39-L49

import Definitions.Def_ReciprocityTheory_DualLattices_WtGtRowSubstXSub
import Definitions.Def_ReciprocityTheory_DualLattices_FischerSelfNeZero
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
open scoped Classical
open ReciprocityTheory ReciprocityTheory.PGsh
variable {ν : ℕ} {ι : Type*}

theorem ReciprocityTheory.PGsh.rowSubst_mul (g h : Matrix (Fin ν) (Fin ν) ℂ) (P : MvPolynomial (Fin ν × ι) ℂ) :
    rowSubst h (rowSubst g P) = rowSubst (h * g) P := by sorry
