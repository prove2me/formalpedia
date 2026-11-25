-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_CanonicalLiftUnpacking_alpha_unpack
-- name    : ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftUnpacking.alpha_unpack
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:10.002786+00:00
-- url     : https://prove2.me/theorems/44258762-887b-4aeb-94dc-66c047ad37f9
-- title:
--   Canonical Lift Unpacking: alpha unpack
-- statement:
--   The Canonical Lift Unpacking construction uses the alpha unpack property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/CanonicalLiftUnpacking.lean#L44-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/CanonicalLiftUnpacking.lean#L44-L77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_CanonicalLiftUnpacking
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftUnpacking
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftUnpacking.alpha_unpack {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
    [IsDomain V] [IsDiscreteValuationRing V] {t : SAB H (Sp V)} (P : PELUnif (maximalIdeal V) t)
    (hT : P.TorsionIso) (hQ : QkActExistsStatement) (α : 𝓞 E) (N : ℕ) (hN : 1 ≤ N)
    (hαN : letI := H.starRing; α * star α = (N : 𝓞 E)) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing V) F] (p : QkPt P.D.toPre F (1 * N)) (x : TFK (R := V) F ⟶ P.A.A)
    (hx : P.ToA F (1 * N) p x) (hxα : x ≫ P.oA.act α = 1) :
    letI := H.starRing
    ∃ (z : P.D.toPre.X) (q : QkPt P.D.toPre F (1 * N)) (h g0 : GtPtF P.D.toPre F),
      p.y = -(star α • z) ∧ GtAct P.oD α p.g q.g ∧ GtPtF.IsIota z h ∧ q.g.IsAdd h g0 ∧ g0.IsZero := by sorry
