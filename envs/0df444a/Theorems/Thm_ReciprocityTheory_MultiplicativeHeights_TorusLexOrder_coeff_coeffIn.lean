-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_coeff_coeffIn
-- name    : ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.coeff_coeffIn
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:10.353289+00:00
-- url     : https://prove2.me/theorems/03d553e1-0b87-52d5-9505-171d1c271933
-- title:
--   Torus Lex Order: coeff coeff In
-- statement:
--   The Torus Lex Order construction uses the coeff coeff In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusLexA.lean#L25-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusLexA.lean#L25-L47

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.TorusLexOrder

theorem ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.coeff_coeffIn {ι : Type} (i : ι) (k : ℕ) (f : MvPolynomial ι ℂ) (u : ι →₀ ℕ) :
    (coeffIn i k f).coeff u = if u i = 0 then f.coeff (u + Finsupp.single i k) else 0 := by sorry
