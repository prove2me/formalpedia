-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_quad_conj
-- name    : ReciprocityTheory.MultiplicativeHeights.sdd_quad_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:30.190937+00:00
-- url     : https://prove2.me/theorems/57477834-5ffa-478f-ad74-fa42613a1e85
-- title:
--   Multiplicative Heights: sdd quad conj
-- statement:
--   The Multiplicative Heights construction uses the sdd quad conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDA.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDA.lean#L10-L13

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

theorem ReciprocityTheory.MultiplicativeHeights.sdd_quad_conj {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (w : Fin m → ℂ) :
    star w ⬝ᵥ ((Pᴴ * Q * P) *ᵥ w) = star (P *ᵥ w) ⬝ᵥ (Q *ᵥ (P *ᵥ w)) := by sorry
