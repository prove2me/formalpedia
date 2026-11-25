-- Prove2me | Theorems.Thm_PI_ScRefExists_TH_cj_ne
-- name    : PI.ScRefExists.TH.cj_ne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:27:18.121357+00:00
-- url     : https://prove2.me/theorems/c3825307-4846-5443-9bda-714cb6fb797a
-- title:
--   TH: cj ne
-- statement:
--   The TH construction uses the cj ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/ThetaA.lean#L73-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/ThetaA.lean#L73-L118

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.TH
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.ScRefExists.TH.cj_ne (g : ℕ) (hg : 1 ≤ g) (hS : PI.ScRefExists.Sk.SplitG I g) (P : HeightOneSpectrum (𝓞 I.E))
    (hP : (g : 𝓞 I.E) ∈ P.asIdeal) : cj I P ≠ P := by sorry
