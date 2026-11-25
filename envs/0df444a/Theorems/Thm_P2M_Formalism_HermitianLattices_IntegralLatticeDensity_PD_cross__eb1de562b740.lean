-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cross__eb1de562b740
-- name    : P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cross__eb1de562b740
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:18.345139+00:00
-- url     : https://prove2.me/theorems/411725f6-3dea-4320-8e7b-76a3095ed3e6
-- title:
--   P2 M Formalism Hermitian Lattices Integral Lattice Density PD cross  eb1de562b740: P2 M Formalism Hermitian Lattices Integral Lattice Density PD cross  eb1de562b740
-- statement:
--   The P2 M Formalism Hermitian Lattices Integral Lattice Density PD cross  eb1de562b740 construction uses the P2 M Formalism Hermitian Lattices Integral Lattice Density PD cross  eb1de562b740 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean#L58-L66

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

theorem P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cross__eb1de562b740 (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    (h2 : ∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b))
    {n J : Type} [Fintype n] (c : n → O) (d : n → J → O) (a : M) (s : Finset J) (x : J → M) :
    ∑ i, cob φ (c i • a) (∑ j ∈ s, d i j • x j) =
      ∑ j ∈ s, cob φ a ((∑ i, star (c i) * d i j) • x j) := by sorry

alias «Formalism».«HermitianLattices».«IntegralLatticeDensity».«PD».«cross'» := P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cross__eb1de562b740
