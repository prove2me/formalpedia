-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_amat_sub
-- name    : PI.UnitaryGroupMassFormula.LCG.amat_sub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:39:34.138806+00:00
-- url     : https://prove2.me/theorems/d0cdfe34-fb6a-4016-8960-6900f39461d3
-- title:
--   LCG: amat sub
-- statement:
--   The LCG construction uses the amat sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/LatCountAllOf.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/LatCountAllOf.lean#L45-L49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_LatCountAllOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.LatCountG

theorem PI.UnitaryGroupMassFormula.LCG.amat_sub (I : Formalism.MainNotions.S.AutInst) (x y : I.GA) (v : InfinitePlace I.F) (δ₁ δ₂ : Matrix (Fin I.n) (Fin I.n) I.E) :
    amat I x y v (δ₁ - δ₂) = amat I x y v δ₁ - amat I x y v δ₂ := by sorry
