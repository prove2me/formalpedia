-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_add_right__9a421b50c142
-- name    : P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_add_right__9a421b50c142
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:54.93688+00:00
-- url     : https://prove2.me/theorems/a64f8d71-8e5a-4e71-a819-e41c0a3b62e8
-- title:
--   P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob add right  9a421b50c142: P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob add right  9a421b50c142
-- statement:
--   The P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob add right  9a421b50c142 construction uses the P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob add right  9a421b50c142 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean#L21-L23

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

theorem P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_add_right__9a421b50c142 (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) (a b b' : M) :
    cob φ a (b + b') = cob φ a b + cob φ a b' := by sorry

alias «Formalism».«HermitianLattices».«IntegralLatticeDensity».«PD».«cob_add_right'» := P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_add_right__9a421b50c142
