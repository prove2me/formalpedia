-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isPullUnif_of_uniq
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.isPullUnif_of_uniq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:58:30.800397+00:00
-- url     : https://prove2.me/theorems/4f23d753-44a0-5503-9ccc-67afb8c2f65b
-- title:
--   Tor: is Pull Unif of uniq
-- statement:
--   The Tor construction uses the is Pull Unif of uniq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/CocycleIdentityIso.lean#L250-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/CocycleIdentityIso.lean#L250-L323

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

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
open ReciprocityTheory.ChartRestriction.G.Out

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.isPullUnif_of_uniq {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
    {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : Unif I D A G) (U' : Unif I D' A' G) (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre)
    (wL : LB.Iso U'.LG.L U.LG.L) (hwg : wL.IsGen)
    (hwm : LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig U.LG.rig)
    (hlev : ∀ n : ℕ,
      (U'.gt n).pG.left ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
        (U.gt n).pG.left ∧
      (∀ x : D'.toPre.X, ∃ hψ : ∀ k : Fin 4,
          D'.toPre.Oφ ((U'.gt n).pG) x k ≫ hD.e.hom.left ≫
              pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
            𝟙 _ ≫ D.toPre.Oφ ((U.gt n).pG) (hD.xe x) k,
        LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) ((U'.gt n).t x)
          (GeneratorPullback.pullAlong D.toPre.P.L (hD.e.hom.left ≫
                            pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) (𝟙 _) _
            Oinvε _ hψ ((U.gt n).t (hD.xe x)))) ∧
      ∀ (jM : PUnit → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jL : U.LG.L.ι),
        res (X := (thickObj R I n G).left) (inf_le_left.trans (inf_le_left.trans inf_le_left) :
            (U'.gt n).pG.left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (hD.e.hom.left ≫
                pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)))) D'.toPre.P.L).U (jM, jM') ⊓
              (LB.div (D'.toPre.P.L.pull (U'.gt n).pG.left) (U'.LG.L.pull (fstG I n G).left)).U
                (fun _ => jM', fun _ => jL') ⊓
              (LB.div (D.toPre.P.L.pull (U.gt n).pG.left) (U.LG.L.pull (fstG I n G).left)).U
                (jM, fun _ => jL) ⊓
              (fstG I n G).left ⁻¹ᵁ (LB.div U.LG.L U'.LG.L).U (jL, jL') ≤
            (U'.gt n).pG.left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (hD.e.hom.left ≫
                pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)))) D'.toPre.P.L).U (jM, jM'))
          (pullU (U'.gt n).pG.left _ (hD.w.s (jM, jM'))) *
        res (X := (thickObj R I n G).left) (inf_le_left.trans (inf_le_left.trans inf_le_right))
          ((U'.w n).s (fun _ => jM', fun _ => jL')) =
        res (X := (thickObj R I n G).left) (inf_le_left.trans inf_le_right)
          ((U.w n).s (jM, fun _ => jL)) *
        res (X := (thickObj R I n G).left) inf_le_right
          (pullU (fstG I n G).left _ (wL.s (jL, jL'))))
    (bc : G ≅ (Over.pullback (specOf (RingHom.id R))).obj G)
    (hbc : bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = 𝟙 _) :
    IsPullUnif (RingHom.id R) hD bc U U' := by sorry
