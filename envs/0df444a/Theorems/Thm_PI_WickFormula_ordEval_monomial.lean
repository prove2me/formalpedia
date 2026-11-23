-- Prove2me | Theorems.Thm_PI_WickFormula_ordEval_monomial
-- name    : PI.WickFormula.ordEval_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:25.377191+00:00
-- url     : https://prove2.me/theorems/e1dfeb10-fdcf-4dfa-b7ea-22d3edec5326
-- title:
--   Wick Formula: ord Eval monomial
-- statement:
--   The Wick Formula construction uses the ord Eval monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/OrdEvalEqSumOf.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/OrdEvalEqSumOf.lean#L72-L75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula
variable {k AA : Type} [CommRing k] [Ring AA] [Algebra k AA] {r s : ℕ}

theorem PI.WickFormula.ordEval_monomial (a : Fin r → AA) (a' : Fin s → AA) (m : Fin r ⊕ Fin s →₀ ℕ) (c : k) :
    ordEval a a' (monomial m c) = c • omon a a' m := by sorry
