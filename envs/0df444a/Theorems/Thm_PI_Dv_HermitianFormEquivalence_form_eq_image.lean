-- Prove2me | Theorems.Thm_PI_Dv_HermitianFormEquivalence_form_eq_image
-- name    : PI.Dv.HermitianFormEquivalence.form_eq_image
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:55.962958+00:00
-- url     : https://prove2.me/theorems/9a516bd4-9b0a-40f0-a3b0-6642bac062d7
-- title:
--   Hermitian Form Equivalence: form eq image
-- statement:
--   The Hermitian Form Equivalence construction uses the form eq image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceFormEquality/FormEqImage.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceFormEquality/FormEqImage.lean#L22-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_ExistsSumEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_FormEqImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.HermitianFormEquivalence
open PI.Dv
variable {K : Type} [Field K] {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G] {T : GoodSet K G}
  {EE : Type} [AddCommGroup EE] [Module ℂ EE] {ρE : Representation ℂ G EE}

theorem PI.Dv.HermitianFormEquivalence.form_eq_image (M : GMap K σ G T EE ρE) (a : MonoidAlgebra K G) :
    M.form a = (fun z => ∑ g : G, σ (a.coeff g) • ρE g z) '' M.form 1 := by sorry
