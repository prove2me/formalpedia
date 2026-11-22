-- Prove2me | Theorems.Thm_PI_GGConvScalarW_gam_conj
-- name    : PI.GGConvScalarW.gam_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:05.072388+00:00
-- url     : https://prove2.me/theorems/53148392-bfab-4384-84cb-3207809542d6
-- title:
--   GGConv Scalar W: gam conj
-- statement:
--   The GGConv Scalar W construction uses the gam conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/Reindex.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/Reindex.lean#L12-L20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_CardUNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_Reindex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic Finset

theorem PI.GGConvScalarW.gam_conj {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ) (g x : GL (Fin k) F) :
    gam ψ₀ (g * x * g⁻¹) = gam ψ₀ x := by sorry
