-- Prove2me | Theorems.Thm_PI_Dv_HermitianFormEquivalence_phi_apply
-- name    : PI.Dv.HermitianFormEquivalence.phi_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:58.710654+00:00
-- url     : https://prove2.me/theorems/d0ac91ad-18b0-5edb-9eb3-488f0ae16aaa
-- title:
--   Hermitian Form Equivalence: phi apply
-- statement:
--   The Hermitian Form Equivalence construction uses the phi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceFormEquality/ExistsSumEqOne.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceFormEquality/ExistsSumEqOne.lean#L25-L28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_ExistsSumEqOne
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
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.HermitianFormEquivalence.phi_apply (T : GoodSet K G) (s : T.S) (f : Module.End K (T.W s)) :
    phi T s f = ∑ y : G, ((((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K)) *
      LinearMap.trace K (T.W s) (f * T.tau s y⁻¹)) • MonoidAlgebra.of K G y := by sorry
