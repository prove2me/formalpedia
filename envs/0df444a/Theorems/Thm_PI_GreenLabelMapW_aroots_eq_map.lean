-- Prove2me | Theorems.Thm_PI_GreenLabelMapW_aroots_eq_map
-- name    : PI.GreenLabelMapW.aroots_eq_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:56.19899+00:00
-- url     : https://prove2.me/theorems/d2cf3c38-a43d-4256-bee7-a93f69f6ec5c
-- title:
--   Green Label Map W: aroots eq map
-- statement:
--   The Green Label Map W construction uses the aroots eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/RootPowCard.lean#L57-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/RootPowCard.lean#L57-L81

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IntermediateField
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K]

theorem PI.GreenLabelMapW.aroots_eq_map {P : K[X]} (hm : P.Monic) (hi : Irreducible P) {w : AlgebraicClosure K}
    (hw : aeval w P = 0) (f : AlgebraicClosure K → AlgebraicClosure K)
    (hf : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure K),
      f (σ x) = σ (f x))
    (hinj : ∀ r₁ r₂ : AlgebraicClosure K, aeval r₁ P = 0 → aeval r₂ P = 0 → f r₁ = f r₂ → r₁ = r₂) :
    (minpoly K (f w)).aroots (AlgebraicClosure K) = (P.aroots (AlgebraicClosure K)).map f := by sorry
