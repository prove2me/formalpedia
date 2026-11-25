-- Prove2me | Theorems.Thm_PI_ScRefExists_WF_proj_span
-- name    : PI.ScRefExists.WF.proj_span
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:38:12.176044+00:00
-- url     : https://prove2.me/theorems/2014637e-5cd5-492f-8308-bbc0d9224a28
-- title:
--   WF: proj span
-- statement:
--   The WF construction uses the proj span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/MemLAOfNsmul.lean#L181-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/MemLAOfNsmul.lean#L181-L194

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_MemLAOfNsmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open PI PI.ScRefExists PI.ScRefExists.WF
variable {I : Formalism.MainNotions.S.AutInst} {p : ℕ}

theorem PI.ScRefExists.WF.proj_span {r : ℕ} (e f : Fin r → Fin I.n → I.E) (hp : p.Prime)
    (heA : ∀ a, e a ∈ LA I p) (hfA : ∀ a, f a ∈ LA I p) {y : Fin I.n → I.E} (hy : y ∈ LA I p)
    (S : Set (Fin I.n → I.E)) (hS : Set.range e ∪ Set.range f ⊆ S) :
    proj e f y ∈ Submodule.span (Ap I p) S := by sorry
