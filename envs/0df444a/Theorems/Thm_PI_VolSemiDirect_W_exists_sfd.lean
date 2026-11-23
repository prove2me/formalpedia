-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_exists_sfd
-- name    : PI.VolSemiDirect.W.exists_sfd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:49:24.652648+00:00
-- url     : https://prove2.me/theorems/8ae2c75b-0e0e-46ed-a873-cdac7e888004
-- title:
--   W: exists sfd
-- statement:
--   The W construction uses the exists sfd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/FundamentalDomainExists.lean#L10-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/FundamentalDomainExists.lean#L10-L88

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_FundamentalDomainExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open MeasureTheory

theorem PI.VolSemiDirect.W.exists_sfd {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Λ : Subgroup G)
    [DiscreteTopology Λ] :
    ∃ 𝓕 : Set G, MeasurableSet 𝓕 ∧ ∀ x : G, ∃! γ : Λ, γ • x ∈ 𝓕 := by sorry
