-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_sum_right__f70a37db6225
-- name    : P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_sum_right__f70a37db6225
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:56:37.147844+00:00
-- url     : https://prove2.me/theorems/4a726960-68a5-480f-a2c7-e42a619572fc
-- title:
--   P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob sum right  f70a37db6225: P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob sum right  f70a37db6225
-- statement:
--   The P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob sum right  f70a37db6225 construction uses the P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob sum right  f70a37db6225 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean#L42-L47

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

theorem P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_sum_right__f70a37db6225 (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    {J : Type} (a : M) (s : Finset J) (x : J → M) :
    cob φ a (∑ j ∈ s, x j) = ∑ j ∈ s, cob φ a (x j) := by sorry

alias «Formalism».«HermitianLattices».«IntegralLatticeDensity».«PD».«cob_sum_right'» := P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_sum_right__f70a37db6225
