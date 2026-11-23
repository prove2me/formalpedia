-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_phi_add__97db315ad562
-- name    : P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_phi_add__97db315ad562
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:37.549034+00:00
-- url     : https://prove2.me/theorems/b1bb85d4-2b7d-4c3e-b38b-32cb126a41f5
-- title:
--   P2 M Formalism Hermitian Lattices Integral Lattice Density PD phi add  97db315ad562: P2 M Formalism Hermitian Lattices Integral Lattice Density PD phi add  97db315ad562
-- statement:
--   The P2 M Formalism Hermitian Lattices Integral Lattice Density PD phi add  97db315ad562 construction uses the P2 M Formalism Hermitian Lattices Integral Lattice Density PD phi add  97db315ad562 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean#L17-L19

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

theorem P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_phi_add__97db315ad562 (a b : M) : φ (a + b) = φ a + φ b + cob φ a b := by sorry

alias «Formalism».«HermitianLattices».«IntegralLatticeDensity».«PD».«phi_add'» := P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_phi_add__97db315ad562
