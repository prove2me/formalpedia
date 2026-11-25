-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HolTorsion_valAt__eq_of_pow_eq_one_6fce98a090c1
-- name    : P2M_GlobalTheory_HolTorsion_valAt__eq_of_pow_eq_one_6fce98a090c1
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:06:25.881802+00:00
-- url     : https://prove2.me/theorems/b8630730-d80b-4ae0-92e5-e5f76aa645d0
-- title:
--   P2 M Global Theory Hol Torsion val At  eq of pow eq one 6fce98a090c1: P2 M Global Theory Hol Torsion val At  eq of pow eq one 6fce98a090c1
-- statement:
--   The P2 M Global Theory Hol Torsion val At  eq of pow eq one 6fce98a090c1 construction uses the P2 M Global Theory Hol Torsion val At  eq of pow eq one 6fce98a090c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionEqAndWeilIsOfIsHolTo.lean#L111-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionEqAndWeilIsOfIsHolTo.lean#L111-L118

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionEqAndWeilIsOfIsHolTo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.HolTorsion
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E}

theorem P2M_GlobalTheory_HolTorsion_valAt__eq_of_pow_eq_one_6fce98a090c1 {Z : Scheme.{0}} {c : E → (Sp ℂ ⟶ Z)} (hc : IsHolTo B c) (hB : IsPreconnected B)
    {e : Γ(Z, ⊤)} {k : ℕ} (hk : 0 < k) (he : e ^ k = 1) {b₀ b : E} (hb₀ : b₀ ∈ B) (hb : b ∈ B) :
    valAt' (c b) ⊤ e = valAt' (c b₀) ⊤ e := by sorry

alias «GlobalTheory».«HolTorsion».«valAt'_eq_of_pow_eq_one» := P2M_GlobalTheory_HolTorsion_valAt__eq_of_pow_eq_one_6fce98a090c1
