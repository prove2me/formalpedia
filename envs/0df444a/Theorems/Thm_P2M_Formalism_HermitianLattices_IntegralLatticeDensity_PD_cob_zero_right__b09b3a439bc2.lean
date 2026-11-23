-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_zero_right__b09b3a439bc2
-- name    : P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_zero_right__b09b3a439bc2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:16.275796+00:00
-- url     : https://prove2.me/theorems/c8ffd3e7-3194-44a2-910c-27f49581be1f
-- title:
--   P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob zero right  b09b3a439bc2: P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob zero right  b09b3a439bc2
-- statement:
--   The P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob zero right  b09b3a439bc2 construction uses the P2 M Formalism Hermitian Lattices Integral Lattice Density PD cob zero right  b09b3a439bc2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean#L33-L35

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

theorem P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_zero_right__b09b3a439bc2 (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) (a : M) :
    cob φ a 0 = 0 := by sorry

alias «Formalism».«HermitianLattices».«IntegralLatticeDensity».«PD».«cob_zero_right'» := P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_zero_right__b09b3a439bc2
