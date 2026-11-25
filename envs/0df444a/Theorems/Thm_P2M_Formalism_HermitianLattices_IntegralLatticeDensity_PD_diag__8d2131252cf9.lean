-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_diag__8d2131252cf9
-- name    : P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_diag__8d2131252cf9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:14.570779+00:00
-- url     : https://prove2.me/theorems/9e2f3ba9-68ae-41c1-afcc-707d2b0a99bf
-- title:
--   P2 M Formalism Hermitian Lattices Integral Lattice Density PD diag  8d2131252cf9: P2 M Formalism Hermitian Lattices Integral Lattice Density PD diag  8d2131252cf9
-- statement:
--   The P2 M Formalism Hermitian Lattices Integral Lattice Density PD diag  8d2131252cf9 construction uses the P2 M Formalism Hermitian Lattices Integral Lattice Density PD diag  8d2131252cf9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean#L70-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean#L70-L88

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HyperbolicPlaneSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.IntegralLatticeDensity Formalism.HermitianLattices.IntegralLatticeDensity.PD
open Finset Formalism.HermitianLattices.IntegralLatticeDensity
variable {M Q : Type} [AddCommGroup M] [AddCommGroup Q] {φ : M → Q}
variable {O : Type} [CommRing O] [StarRing O] [Module O M]
variable {Z : Type} [CommRing Z] [Module Z Q] {nm : O → Z}

theorem P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_diag__8d2131252cf9 (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    (h2 : ∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b))
    (h3 : ∀ (α : O) u, φ (α • u) = nm α • φ u)
    {n J : Type} [Fintype n] (c : n → J → O)
    (hG : ∀ a j, a ≠ j → ∑ i, star (c i a) * c i j = 0) (u : J → M) (s : Finset J) :
    ∑ i, φ (∑ j ∈ s, c i j • u j) = ∑ j ∈ s, (∑ i, nm (c i j)) • φ (u j) := by sorry

alias «Formalism».«HermitianLattices».«IntegralLatticeDensity».«PD».«diag'» := P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_diag__8d2131252cf9
