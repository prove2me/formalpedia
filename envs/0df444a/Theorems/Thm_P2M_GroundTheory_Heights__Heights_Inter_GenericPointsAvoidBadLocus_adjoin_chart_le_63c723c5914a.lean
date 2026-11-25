-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_GenericPointsAvoidBadLocus_adjoin_chart_le_63c723c5914a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_GenericPointsAvoidBadLocus_adjoin_chart_le_63c723c5914a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:10:12.820002+00:00
-- url     : https://prove2.me/theorems/cdb077a1-0bf7-4944-a07d-a2f9dd39d5b2
-- title:
--   P2 M Ground Theory Heights  Heights Inter Generic Points Avoid Bad Locus adjoin chart le 63c723c5914a: P2 M Ground Theory Heights  Heights Inter Generic Points Avoid Bad Locus adjoin chart le 63c723c5
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Generic Points Avoid Bad Locus adjoin chart le 63c723c5914a construction uses the P2 M Ground Theory Heights  Heights Inter Generic Points Avoid Bad Locus adjoin chart le 63c723c5914a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogProdInt.lean#L37-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogProdInt.lean#L37-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOverChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogProdInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_GenericPointsAvoidBadLocus_adjoin_chart_le_63c723c5914a {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
    (G : GenFibre v P') (i j : ∀ k : FibreBlock κ, ι' k.1) (hi : ∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0) :
    IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) ≤
      IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«GenericPointsAvoidBadLocus».«adjoin_chart_le» := P2M_GroundTheory_Heights__Heights_Inter_GenericPointsAvoidBadLocus_adjoin_chart_le_63c723c5914a
