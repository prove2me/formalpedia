-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_null_of_logBound
-- name    : ReciprocityTheory.MultiplicativeHeights.null_of_logBound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:07.136155+00:00
-- url     : https://prove2.me/theorems/e6605963-1fa1-40cc-bb04-53534ddf1b19
-- title:
--   Multiplicative Heights: null of log Bound
-- statement:
--   The Multiplicative Heights construction uses the null of log Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L45-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L45-L98

import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
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
open MeasureTheory MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.null_of_logBound {B n : ℕ} (hn : 0 < n) (hInt : SphereLogIntegrableStatement)
    (hbound : ∀ (a : Fin B → ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ) (u : BlockSphere B n),
      IsMultiHomogeneous a g → eval (blockPoint u) g ≠ 0 →
      Real.log ‖eval (blockPoint u) g‖ - (∑ b, (a b : ℝ)) / 2 * (harmonic (n - 1) : ℝ) ≤
        blockSphereMean B n g)
    (a : Fin B → ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ) (u : BlockSphere B n)
    (hg : IsMultiHomogeneous a g) (hu : eval (blockPoint u) g ≠ 0) :
    blockSphereProb B n {z | eval (blockPoint z) g = 0} = 0 := by sorry
