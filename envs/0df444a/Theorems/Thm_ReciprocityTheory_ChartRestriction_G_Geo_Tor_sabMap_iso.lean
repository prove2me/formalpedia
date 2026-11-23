-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sabMap_iso
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.sabMap_iso
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:58.65081+00:00
-- url     : https://prove2.me/theorems/6e1a69f2-4741-456c-a4c0-d0c51bacaa48
-- title:
--   Tor: sab Map iso
-- statement:
--   The Tor construction uses the sab Map iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/SabMapCubical.lean#L25-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/SabMapCubical.lean#L25-L42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabMapCubical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.sabMap_iso {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f : S' ⟶ S} (m₁ : SABMap t₁ t f)
    (m₂ : SABMap t₂ t f) {L₁ : RigLB t₁.G} {L₂ : RigLB t₂.G} (h₁ : L₁ = t₁.PP) (h₂ : L₂ = t₂.PP) :
    ∃ ψ : t₁.G ≅ t₂.G, IsMonHom ψ.hom ∧ ψ.hom.left ≫ m₂.φ = m₁.φ ∧
      (∀ x, t₁.act.act x ≫ ψ.hom = ψ.hom ≫ t₂.act.act x) ∧
      ∃ (he : eSec t₁.G ≫ ψ.hom.left = 𝟙 _ ≫ eSec t₂.G) (wL : LB.Iso L₁.L (L₂.L.pull ψ.hom.left)),
        wL.IsGen ∧ LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec t₁.G) (fun _ => 1)) L₁.rig
          (rigPullOf ψ.hom.left (𝟙 _) he L₂.L L₂.rig) := by sorry
