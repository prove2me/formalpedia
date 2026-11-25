-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCA_conjNH_of
-- name    : PI.LevelKSplit.W.NCA.conjNH_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:38:59.917674+00:00
-- url     : https://prove2.me/theorems/cb545b74-41a1-4df3-8907-b4f9398d1d89
-- title:
--   NCA: conj NH of
-- statement:
--   The NCA construction uses the conj NH of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/NCAsmM.lean#L27-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/NCAsmM.lean#L27-L130

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCAsmV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCAsmM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open PI.LevelKSplit PI.LevelKSplit.W.NC PI.LevelKSplit.W.SemiA PI.VolSemiDirect.W
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem PI.LevelKSplit.W.NCA.conjNH_of (hC : NCoord F E σ M J) (hV : PI.LevelKSplit.W.CD.ModV F E σ M J) :
    PI.LevelKSplit.W.ExS.ConjNH F E σ M J := by sorry
