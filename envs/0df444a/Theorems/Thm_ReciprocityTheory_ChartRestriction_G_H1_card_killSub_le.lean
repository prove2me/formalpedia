-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_card_killSub_le
-- name    : ReciprocityTheory.ChartRestriction.G.H1.card_killSub_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:03:47.587497+00:00
-- url     : https://prove2.me/theorems/8ee7ac54-ddc6-48f0-9f85-4018b6e85f06
-- title:
--   H1: card kill Sub le
-- statement:
--   The H1 construction uses the card kill Sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/AlphaBarEnum.lean#L32-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/AlphaBarEnum.lean#L32-L78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_AlphaPair
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_AlphaBarEnum
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem ReciprocityTheory.ChartRestriction.G.H1.card_killSub_le (hW : WeilSt) (A : PolAV (Sp (FractionRing R))) {O : Type} [Ring O] (ρ : RingAct A.A O)
    (N : ℕ) (ga gb : O) (hga : ∀ x ∈ killSub F A ρ ga, x ^ N = 1) (hgb : ∀ z ∈ killSub F A ρ gb, z ^ N = 1)
    [Finite (killSub F A ρ ga)] [Finite (killSub F A ρ gb)]
    (sep : ∀ x ∈ killSub F A ρ ga, ∀ x' ∈ killSub F A ρ ga, x ≠ x' → ∃ z ∈ killSub F A ρ gb,
      ∃ c c' : Γ((TFK (R := R) F).left, ⊤)ˣ,
        WeilIs A.A A.L N z x c ∧ WeilIs A.A A.L N z x' c' ∧ c ≠ c') :
    Nat.card (killSub F A ρ ga) ≤ Nat.card (killSub F A ρ gb) := by sorry
