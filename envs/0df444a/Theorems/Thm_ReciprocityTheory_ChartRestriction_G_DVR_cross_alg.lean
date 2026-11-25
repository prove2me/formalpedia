-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cross_alg
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.cross_alg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:13.423591+00:00
-- url     : https://prove2.me/theorems/a9055e57-103b-532d-b2a0-d67104238592
-- title:
--   DVR: cross alg
-- statement:
--   The DVR construction uses the cross alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/MemFinsetInf.lean#L25-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/MemFinsetInf.lean#L25-L42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RsAppPullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_MemFinsetInf
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem ReciprocityTheory.ChartRestriction.G.DVR.cross_alg {Γ : Type} [CommRing Γ] {Jx Xc : Type} [DecidableEq Xc] (S : Finset Jx) (S'' : Finset Xc)
    (g : Jx → Xc) (hg : Set.InjOn g S) (hS : S.image g ⊆ S'') (W W' : Γˣ) (m n : ℕ) (Z Y : Fin 2 → Γ)
    (P1 : Fin 2 → Xc → Γ) (P2 A : Fin 2 → Jx → Γ) (c : Jx → Γ) (ξ : Γ)
    (E1 : ∀ i, (W : Γ) ^ m * Z i = ∑ β ∈ S'', P1 i β)
    (E2 : ∀ i, (W' : Γ) ^ n * Y i = ∑ α ∈ S, P2 i α)
    (E1' : ∀ i, ∀ χ ∈ S, P1 i (g χ) = A i χ * ξ * c χ)
    (E2' : ∀ i, ∀ α ∈ S, P2 i α = A i α * c α)
    (E5 : ∀ i, ∀ β ∈ S'', β ∉ S.image g → P1 i β = 0) :
    Z 0 * Y 1 - Z 1 * Y 0 = 0 := by sorry
