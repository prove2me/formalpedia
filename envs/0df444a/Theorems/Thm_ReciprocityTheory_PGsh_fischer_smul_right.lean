-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_fischer_smul_right
-- name    : ReciprocityTheory.PGsh.fischer_smul_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:20.802695+00:00
-- url     : https://prove2.me/theorems/fcc8fefd-d1a0-4faf-8723-b882e700e3ee
-- title:
--   PGsh: fischer smul right
-- statement:
--   The PGsh construction uses the fischer smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FischerSmulRight.lean#L110-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FischerSmulRight.lean#L110-L116

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_FischerSmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open scoped Classical
open ReciprocityTheory ReciprocityTheory.PGsh
variable {ν : ℕ} {ι : Type*}

theorem ReciprocityTheory.PGsh.fischer_smul_right (c : ℂ) (P Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer P (c • Q) = starRingEnd ℂ c * fischer P Q := by sorry
