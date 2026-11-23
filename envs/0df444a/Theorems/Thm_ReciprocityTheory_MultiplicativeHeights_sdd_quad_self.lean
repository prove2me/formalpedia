-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_quad_self
-- name    : ReciprocityTheory.MultiplicativeHeights.sdd_quad_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:44.820061+00:00
-- url     : https://prove2.me/theorems/628fd55b-fc3b-4fee-aa27-97203314c2c5
-- title:
--   Multiplicative Heights: sdd quad self
-- statement:
--   The Multiplicative Heights construction uses the sdd quad self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDA.lean#L73-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDA.lean#L73-L79

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

theorem ReciprocityTheory.MultiplicativeHeights.sdd_quad_self {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit B.det) (w : Fin n → ℂ) :
    star w ⬝ᵥ w = star (B⁻¹ *ᵥ w) ⬝ᵥ ((Bᴴ * B) *ᵥ (B⁻¹ *ᵥ w)) := by sorry
