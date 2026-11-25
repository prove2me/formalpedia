-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_derivExists_of_split
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.derivExists_of_split
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:41:17.939793+00:00
-- url     : https://prove2.me/theorems/b33640c4-f601-43d9-a1cc-dbd108ca5673
-- title:
--   HW: deriv Exists of split
-- statement:
--   The HW construction uses the deriv Exists of split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/DerivK.lean#L28-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/DerivK.lean#L28-L64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Blocks
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.HW.derivExists_of_split (h : DerivExistsAllPosStatement) (ε : Fin n → Bool)
    (p : Bool → ℕ) (emb : ∀ s, KG (fun _ : Fin (p s) => true) →* KG ε)
    (hemb : ∀ s, Continuous (emb s))
    (blk : ∀ s, Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin (p s)) (Fin (p s)) ℂ)
    (hblk : ∀ s X, inK ε X → inK (fun _ : Fin (p s) => true) (blk s X))
    (hsplit : ∀ X (hX : inK ε X) (t : ℝ),
      toMK (emb true (onepCurve _ (hblk true X hX) t)) *
          toMK (emb false (onepCurve _ (hblk false X hX) t)) =
        NormedSpace.exp ((t : ℂ) • X))
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (τ : KG ε →* unitary (V →L[ℂ] V)) (hτ : Continuous τ) :
    ∃ dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V),
      ∀ X, inK ε X → ∀ γ : ℝ → KG ε,
        (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
          HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0 := by sorry
