-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_sum_left__8bececcd4c7e
-- name    : P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_sum_left__8bececcd4c7e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:49.647596+00:00
-- url     : https://prove2.me/theorems/82e672e3-3d8d-4923-9db9-de320b5c069e
-- title:
--   P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob sum left  8bececcd4c7e: P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob sum left  8bececcd4c7e
-- statement:
--   The P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob sum left  8bececcd4c7e construction uses the P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob sum left  8bececcd4c7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean#L49-L54

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

theorem P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_sum_left__8bececcd4c7e (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    {J : Type} (b : M) (s : Finset J) (x : J → M) :
    cob φ (∑ j ∈ s, x j) b = ∑ j ∈ s, cob φ (x j) b := by sorry

alias «Formalism».«HermitianLattices».«IntegralLatticeDensity».«PD».«cob_sum_left'» := P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_sum_left__8bececcd4c7e
