-- Prove2me | Theorems.Thm_PI_ScRefExists_WF_fam_sp
-- name    : PI.ScRefExists.WF.fam_sp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:38:41.384285+00:00
-- url     : https://prove2.me/theorems/cd342f76-6037-4da6-af4b-38198a2a344e
-- title:
--   WF: fam sp
-- statement:
--   The WF construction uses the fam sp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/WFrameOf.lean#L53-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/WFrameOf.lean#L53-L83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_MemLAOfNsmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WFrameOf
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
variable {r k : ℕ} {e f : Fin r → Fin I.n → I.E} {w : Fin (k + 1) → Fin I.n → I.E}

theorem PI.ScRefExists.WF.fam_sp (hp : p.Prime) (he : ∀ a b, hG I (e a) (e b) = 0) (hf : ∀ a b, hG I (f a) (f b) = 0)
    (hef : ∀ a b, hG I (e a) (f b) = if a = b then 1 else 0)
    (heA : ∀ a, e a ∈ LA I p) (hfA : ∀ a, f a ∈ LA I p)
    (hW : ∀ x ∈ LA I p, (∀ a, hG I (e a) x = 0 ∧ hG I (f a) x = 0) →
        x ∈ Submodule.span (Ap I p) (Set.range w)) :
    ⊤ ≤ Submodule.span I.E (Set.range (fam e f w)) := by sorry
