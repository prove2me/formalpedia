-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_coeffVec_apply
-- name    : ReciprocityTheory.MultiplicativeHeights.coeffVec_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:26.783983+00:00
-- url     : https://prove2.me/theorems/a077ac09-2bcc-43c2-9082-553e28e2c03a
-- title:
--   Multiplicative Heights: coeff Vec apply
-- statement:
--   The Multiplicative Heights construction uses the coeff Vec apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExpTorusMeanLeL2OfLex.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExpTorusMeanLeL2OfLex.lean#L52-L53

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExpTorusMeanLeL2OfLex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Finset

theorem ReciprocityTheory.MultiplicativeHeights.coeffVec_apply {ι : Type*} (T : Finset (ι →₀ ℕ)) (P : MvPolynomial ι ℂ) (t : T) :
    coeffVec T P t = P.coeff t := by sorry
