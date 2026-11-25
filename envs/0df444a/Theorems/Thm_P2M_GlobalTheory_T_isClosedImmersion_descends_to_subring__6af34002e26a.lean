-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_isClosedImmersion_descends_to_subring__6af34002e26a
-- name    : P2M_GlobalTheory_T_isClosedImmersion_descends_to_subring__6af34002e26a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:09:39.147453+00:00
-- url     : https://prove2.me/theorems/690ab5ff-4665-4cd5-8daa-9f49578c7d0e
-- title:
--   P2 M Global Theory T is Closed Immersion descends to subring  6af34002e26a: P2 M Global Theory T is Closed Immersion descends to subring  6af34002e26a
-- statement:
--   The P2 M Global Theory T is Closed Immersion descends to subring  6af34002e26a construction uses the P2 M Global Theory T is Closed Immersion descends to subring  6af34002e26a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsClosedImmersionDescendsToSubringStatement.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsClosedImmersionDescendsToSubringStatement.lean#L18-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsClosedImmersionDescendsToSubring
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsClosedImmersionDescendsToSubringStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_isClosedImmersion_descends_to_subring__6af34002e26a : ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X₀ Y₀ X Y : Scheme.{0}) (g₀ : X₀ ⟶ Y₀) (q : Y₀ ⟶ Sp R₀) [QuasiCompact q] [QuasiCompact g₀] [QuasiSeparated g₀] [LocallyOfFiniteType g₀] (g : X ⟶ Y) (πX : X ⟶ X₀) (πY : Y ⟶ Y₀) (p : Y ⟶ Sp S), IsPullback πY p q (spMap R₀.subtype) → IsPullback πX g g₀ πY → IsClosedImmersion g → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ Y₁ : Scheme.{0}) (g₁ : X₁ ⟶ Y₁) (πX₁ : X₁ ⟶ X₀) (πY₁ : Y₁ ⟶ Y₀) (p₁ : Y₁ ⟶ Sp R₁), IsPullback πY₁ p₁ q (spMap (Subring.inclusion h)) → IsPullback πX₁ g₁ g₀ πY₁ → IsClosedImmersion g₁ := by sorry

alias «GlobalTheory».«T».«isClosedImmersion_descends_to_subring'» := P2M_GlobalTheory_T_isClosedImmersion_descends_to_subring__6af34002e26a
