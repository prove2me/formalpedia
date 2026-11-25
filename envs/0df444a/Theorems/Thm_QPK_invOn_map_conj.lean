-- Prove2me | Theorems.Thm_QPK_invOn_map_conj
-- name    : QPK.invOn_map_conj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:51:06.28638+00:00
-- url     : https://prove2.me/theorems/9db62fbb-5566-45a3-a750-6d8139c7d96b
-- title:
--   QPK: inv On map conj
-- statement:
--   The QPK construction uses the inv On map conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/ConjugationInvariantMeasure.lean#L39-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/ConjugationInvariantMeasure.lean#L39-L70

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_ConjugationInvariantMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology
open scoped ENNReal
open QPK
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem QPK.invOn_map_conj {N : Set G} (hNc : IsClosed N) (h : G)
    (hn1 : ∀ m ∈ N, h * m * h⁻¹ ∈ N) (hn2 : ∀ m ∈ N, h⁻¹ * m * h⁻¹⁻¹ ∈ N)
    {μ : Measure G} (hμ : InvOn μ N) : InvOn (μ.map (fun x => h * x * h⁻¹)) N := by sorry
