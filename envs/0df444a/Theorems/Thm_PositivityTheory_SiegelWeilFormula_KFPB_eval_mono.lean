-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_eval_mono
-- name    : PositivityTheory.SiegelWeilFormula.KFPB.eval_mono
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:16:53.083326+00:00
-- url     : https://prove2.me/theorems/ff67b014-cecf-5e59-a272-6edf3c27ea61
-- title:
--   KFPB: eval mono
-- statement:
--   The KFPB construction uses the eval mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IntegrablePolyGauss.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IntegrablePolyGauss.lean#L56-L57

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_J_eq
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_J_zero
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_intg_pow_quad
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_pk_deg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped FourierTransform
open MeasureTheory Complex MvPolynomial
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
open PositivityTheory.SiegelWeilFormula.KLI (J pk J_eq J_zero intg_pow_quad pk_deg)
variable {ι : Type} [Fintype ι]

theorem PositivityTheory.SiegelWeilFormula.KFPB.eval_mono (s : ι →₀ ℕ) (y : ι → ℂ) : eval y (monomial s (1 : ℂ)) = ∏ i, y i ^ s i := by sorry
