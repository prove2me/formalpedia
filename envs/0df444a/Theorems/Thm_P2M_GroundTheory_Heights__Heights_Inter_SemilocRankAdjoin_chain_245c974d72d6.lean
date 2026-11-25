-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocRankAdjoin_chain_245c974d72d6
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocRankAdjoin_chain_245c974d72d6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:08.415917+00:00
-- url     : https://prove2.me/theorems/f1fd3a7f-a822-41fe-a5d4-e98728925cb0
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Rank Adjoin chain 245c974d72d6: P2 M Ground Theory Heights  Heights Inter Semiloc Rank Adjoin chain 245c974d72d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Rank Adjoin chain 245c974d72d6 construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Rank Adjoin chain 245c974d72d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocRankAdjoin.lean#L28-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocRankAdjoin.lean#L28-L108

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartScalingIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PAdjoinIndepRelfinrank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFinrankAdjoinRange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankAdjoin
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

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocRankAdjoin_chain_245c974d72d6 (hT : ChartScalingIndep.Statement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K → K'}
    {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} (G : GenFibre v P') (i' : ∀ k', ι' k')
    (F : Type) [Field F] [Algebra F G.Φ] [Algebra F G.Φ'] [IsScalarTower F G.Φ G.Φ'] (hv : IsBlockMap κ v)
    (hx : ∀ k', G.x' ⟨k', i' k'⟩ ≠ 0)
    (hmh : IsMultiHomogIdeal (RingHom.ker (aeval G.x' : MRingOver F ι' →ₐ[F] G.Φ'))) :
    IntermediateField.relfinrank
        (IntermediateField.adjoin F (Set.range ((fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩) ∘ v)))
        (IntermediateField.adjoin F (Set.range fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩)) =
      Module.finrank G.Φ (IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i' q.1.1⟩)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocRankAdjoin».«chain» := P2M_GroundTheory_Heights__Heights_Inter_SemilocRankAdjoin_chain_245c974d72d6
