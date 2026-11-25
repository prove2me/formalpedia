-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_sep_core
-- name    : ReciprocityTheory.ChartRestriction.G.H1.sep_core
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:26.094343+00:00
-- url     : https://prove2.me/theorems/04df7ad3-3c54-4239-ba7d-bcc41eea2f83
-- title:
--   H1: sep core
-- statement:
--   The H1 construction uses the sep core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/AlphaPair.lean#L95-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/AlphaPair.lean#L95-L139

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_AlphaPair
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem ReciprocityTheory.ChartRestriction.G.H1.sep_core (A : PolAV (Sp (FractionRing R))) : letI := H.starRing
    ∀ (oA : A.OAct (𝓞 E)) (Dw : Datum H) (_I : TateIso Dw F (TFK (R := R) F ⟶ A.A) (fun a g => g ≫ oA.act a)
        (fun n g g' c => WeilIs A.A A.L n g g' (unitOn c))) (N : ℕ), 1 ≤ N →
      ∀ β u u' : 𝓞 E, β * star β = (N : 𝓞 E) → u * β + u' * star β = 1 →
      ∀ x x' : TFK (R := R) F ⟶ A.A, x ≫ oA.act (star β) = 1 → x' ≫ oA.act (star β) = 1 → x ≠ x' →
        ∃ z : TFK (R := R) F ⟶ A.A, z ≫ oA.act β = 1 ∧
          ∃ c c' : Γ((TFK (R := R) F).left, ⊤)ˣ,
            WeilIs A.A A.L N z x c ∧ WeilIs A.A A.L N z x' c' ∧ c ≠ c' := by sorry
