-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_BlockTriangularLevi_DiscreteGroups_sglob_LConv_IsWhitTest_sub
-- name    : UpperTheory.Reformulated.B.P6.BlockTriangularLevi.DiscreteGroups.sglob.LConv.IsWhitTest.sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:45.794958+00:00
-- url     : https://prove2.me/theorems/a67ae187-0e93-4e27-904b-2a6e9c5742a6
-- title:
--   Is Whit Test: sub
-- statement:
--   The Is Whit Test construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/BlockTriangularLevi.lean#L112-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/BlockTriangularLevi.lean#L112-L132

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_BlockTriangularLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.BlockTriangularLevi
open scoped Sigma DFunLike EquivLike Equiv Matrix CommSemiring CommRing Membership Set Preorder PartialOrder SemilatticeInf Lattice DistribLattice MulZeroClass Units Semiring HMul MulOne MulOneClass Monoid DivInvMonoid Group OfNat One Inv InvOneClass DivInvOneMonoid DivisionMonoid Subgroup Submonoid Subsemigroup Subtype SetLike MulZeroOneClass MonoidHom OneHom Pi PUnit Fin Finset HAdd AddMonoidWithOne AddGroupWithOne Ring DivisionRing Field CommGroup Circle DivisionSemiring Semifield Complex SeminormedRing SeminormedCommRing NormedCommRing NormedField AddChar Zero HSub

theorem UpperTheory.Reformulated.B.P6.BlockTriangularLevi.DiscreteGroups.sglob.LConv.IsWhitTest.sub :
    ∀ {k : Type} [inst_h0 : Field k] [inst_h1 : TopologicalSpace k] {m : ℕ} {ψ : AddChar k Circle} {f f' : GL (Fin m) k → ℂ}, DiscreteGroups.sglob.LConv.IsWhitTest ψ f → DiscreteGroups.sglob.LConv.IsWhitTest ψ f' → DiscreteGroups.sglob.LConv.IsWhitTest (m := m) ψ fun (g : GL (Fin m) k) ↦ f g - f' g := by sorry
