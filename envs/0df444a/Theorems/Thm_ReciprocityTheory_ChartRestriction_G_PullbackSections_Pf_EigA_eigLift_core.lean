-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_eigLift_core
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.eigLift_core
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:42:44.438217+00:00
-- url     : https://prove2.me/theorems/313a31e2-b940-54e9-b0a5-d55e14e895a9
-- title:
--   Eig A: eig Lift core
-- statement:
--   The Eig A construction uses the eig Lift core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/BiextCoeffSecondLinear.lean#L169-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/BiextCoeffSecondLinear.lean#L169-L238

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_FormalGroupCoeffSecondLinear
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextCoeffSecondLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.eigLift_core {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [Field k]
    [Algebra ℚ k] [Algebra R k] (hRQ : IsRQ (R := R) k) (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h)
    {L Ty : Type} (ty : L → Ty) (χ : Ty → O →+* k) (u : L → Fin d → R)
    (heig : ∀ ℓ a, (dAct k B a).mulVec (fun i => algebraMap R k (u ℓ i)) =
      χ (ty ℓ) a • fun i => algebraMap R k (u ℓ i))
    (hidem : ∀ t : Ty, ∃ (n : ℕ) (b : Fin n → O) (c : Fin n → R), (∑ i, algebraMap R k (c i) * χ t (b i) = 1) ∧
      ∀ a : O, ∃ m : Fin n → Fin n → ℤ, (∀ i, a * b i = ∑ j, m i j • b j) ∧
        ∀ j, ∑ i, (m i j : k) * algebraMap R k (c i) = χ t a * algebraMap R k (c j)) :
    ∃ φ : L → Fin d → R, ∀ ℓ ℓ', (∃ a, χ (ty ℓ) a ≠ χ (ty ℓ') (star a)) →
      ∑ i, (algebraMap R k (φ ℓ' i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i) *
        algebraMap R k (u ℓ i) = 0 := by sorry
