-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFP_entire_laplace
-- name    : PositivityTheory.SiegelWeilFormula.KFP.entire_laplace
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:57:32.476809+00:00
-- url     : https://prove2.me/theorems/0497db7e-5ffd-58cc-89e8-a9a6ce5a4e50
-- title:
--   KFP: entire laplace
-- statement:
--   The KFP construction uses the entire laplace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/RealAdelicFockSpace/PolyGaussOfLines.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/RealAdelicFockSpace/PolyGaussOfLines.lean#L27-L30

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivScale
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrableRexpLin
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_PolyGaussOfLines
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_RealAdelicFockSpace_PolyGaussOfLines
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_entire_laplace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFP

theorem PositivityTheory.SiegelWeilFormula.KFP.entire_laplace {ι : Type} [Fintype ι] (c : ℝ) (hc : 0 < c) (h : 𝓢(EuclideanSpace ℝ ι, ℂ))
    (ξ : EuclideanSpace ℝ ι) :
    Differentiable ℂ (fun z : ℂ => ∫ u, h u * Real.exp (-(c * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ)) := by sorry
