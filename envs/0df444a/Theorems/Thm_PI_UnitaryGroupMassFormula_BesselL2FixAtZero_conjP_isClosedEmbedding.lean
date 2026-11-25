-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BesselL2FixAtZero_conjP_isClosedEmbedding
-- name    : PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjP_isClosedEmbedding
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:40:11.127318+00:00
-- url     : https://prove2.me/theorems/c1e0351c-35c7-42ae-9c1a-79b58f6b0a7a
-- title:
--   Bessel L2 Fix At Zero: conj P is Closed Embedding
-- statement:
--   The Bessel L2 Fix At Zero construction uses the conj P is Closed Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselSquareIntegrable/SchurHpk.lean#L20-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselSquareIntegrable/SchurHpk.lean#L20-L42

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselL2FixAtZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpkAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Closed
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BesselL2FixAtZero
open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal
open PI.UpqRep PI.BesselL2FixAtZero
variable {n : ℕ} (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ)

theorem PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjP_isClosedEmbedding (hP : IsUnit P) : IsClosedEmbedding (conjPrime₂ ε P) := by sorry
