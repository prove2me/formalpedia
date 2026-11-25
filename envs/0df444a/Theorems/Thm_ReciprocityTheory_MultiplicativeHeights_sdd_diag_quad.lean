-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_diag_quad
-- name    : ReciprocityTheory.MultiplicativeHeights.sdd_diag_quad
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:27.943397+00:00
-- url     : https://prove2.me/theorems/72d3c4bc-cd7e-5c43-8d90-7137398f2280
-- title:
--   Multiplicative Heights: sdd diag quad
-- statement:
--   The Multiplicative Heights construction uses the sdd diag quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDA.lean#L168-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDA.lean#L168-L176

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder MatrixOrder

theorem ReciprocityTheory.MultiplicativeHeights.sdd_diag_quad {r : ℕ} (d : Fin r → ℝ) (x : Fin r → ℂ) :
    (star x ⬝ᵥ (diagonal (fun l => (d l : ℂ)) *ᵥ x)).re = ∑ l, d l * ‖x l‖ ^ 2 := by sorry
