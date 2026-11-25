-- Prove2me | Theorems.Thm_PI_Dv_HermitianFormEquivalence_form_one_eq
-- name    : PI.Dv.HermitianFormEquivalence.form_one_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:41.395598+00:00
-- url     : https://prove2.me/theorems/4c663e4c-ff52-5bb1-ada4-eba355e6c30f
-- title:
--   Hermitian Form Equivalence: form one eq
-- statement:
--   The Hermitian Form Equivalence construction uses the form one eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceFormEquality/FormEqImage.lean#L34-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceFormEquality/FormEqImage.lean#L34-L64

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

theorem PI.Dv.HermitianFormEquivalence.form_one_eq (M : GMap K σ G T EE ρE) (P0 : Pair K G) (hM : M1 T P0) :
    M.form 1 = (AddSubgroup.closure {z | ∃ g, ∃ y ∈ M.form (eps P0), z = ρE g y} : Set EE) := by sorry
