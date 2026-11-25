-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_phi_zero__cfc66c2ced32
-- name    : P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_phi_zero__cfc66c2ced32
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:56:36.4057+00:00
-- url     : https://prove2.me/theorems/4f1df054-9c70-45b3-a97a-722656eaf7f0
-- title:
--   P2 M Formalism Hermitian Lattices Integral Lattice Density PD phi zero  cfc66c2ced32: P2 M Formalism Hermitian Lattices Integral Lattice Density PD phi zero  cfc66c2ced32
-- statement:
--   The P2 M Formalism Hermitian Lattices Integral Lattice Density PD phi zero  cfc66c2ced32 construction uses the P2 M Formalism Hermitian Lattices Integral Lattice Density PD phi zero  cfc66c2ced32 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean#L37-L40

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

theorem P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_phi_zero__cfc66c2ced32 (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) : φ 0 = 0 := by sorry

alias «Formalism».«HermitianLattices».«IntegralLatticeDensity».«PD».«phi_zero'» := P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_phi_zero__cfc66c2ced32
