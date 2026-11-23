-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_zero_left__fffdab6f3c0e
-- name    : P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_zero_left__fffdab6f3c0e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:42.342205+00:00
-- url     : https://prove2.me/theorems/7abdfe06-90f1-4c18-a562-c10510d098cb
-- title:
--   P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob zero left  fffdab6f3c0e: P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob zero left  fffdab6f3c0e
-- statement:
--   The P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob zero left  fffdab6f3c0e construction uses the P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob zero left  fffdab6f3c0e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean#L25-L31

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

theorem P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_zero_left__fffdab6f3c0e (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) (b : M) :
    cob φ 0 b = 0 := by sorry

alias «Formalism».«HermitianLattices».«IntegralLatticeDensity».«PD».«cob_zero_left'» := P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_zero_left__fffdab6f3c0e
