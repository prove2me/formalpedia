-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_fischer_sum_left
-- name    : ReciprocityTheory.PGsh.fischer_sum_left
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:09:08.931964+00:00
-- url     : https://prove2.me/theorems/3d63d607-8c31-50bd-b7aa-4f9d48d15ce9
-- title:
--   PGsh: fischer sum left
-- statement:
--   The PGsh construction uses the fischer sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FischerSmulRight.lean#L128-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FischerSmulRight.lean#L128-L136

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

theorem ReciprocityTheory.PGsh.fischer_sum_left {α : Type*} (s : Finset α) (f : α → MvPolynomial (Fin ν × ι) ℂ)
    (Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (∑ i ∈ s, f i) Q = ∑ i ∈ s, fischer (f i) Q := by sorry
