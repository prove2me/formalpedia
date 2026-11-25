-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_sums_eq
-- name    : PI.Dv.ProjGramW.sums_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:58.824802+00:00
-- url     : https://prove2.me/theorems/3f83f684-8f2e-48e9-811e-4d6e3eabcae2
-- title:
--   Proj Gram W: sums eq
-- statement:
--   The Proj Gram W construction uses the sums eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L197-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L197-L202

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.ProjGramW.sums_eq {d : ℕ} (j0 : Fin d) (v : Fin d → K) (r : Fin d → 𝓞 K) (hr : r j0 = 0) :
    ∑ k, r k • famC (stdE (K := K) d) (colOp j0 v) k = ∑ k, r k • stdE d k := by sorry
