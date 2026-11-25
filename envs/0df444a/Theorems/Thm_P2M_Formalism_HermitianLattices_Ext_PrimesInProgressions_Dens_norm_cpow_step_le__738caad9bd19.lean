-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_norm_cpow_step_le__738caad9bd19
-- name    : P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_norm_cpow_step_le__738caad9bd19
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:53:01.33198+00:00
-- url     : https://prove2.me/theorems/7cd2ea3c-69e5-4b3d-ad12-892713254395
-- title:
--   P2 M Formalism Hermitian Lattices Ext Primes In Progressions Dens norm cpow step le  738caad9bd19: P2 M Formalism Hermitian Lattices Ext Primes In Progressions Dens norm cpow step le  738caad9bd19
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext Primes In Progressions Dens norm cpow step le  738caad9bd19 construction uses the P2 M Formalism Hermitian Lattices Ext Primes In Progressions Dens norm cpow step le  738caad9bd19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensPair.lean#L49-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensPair.lean#L49-L64

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

theorem P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_norm_cpow_step_le__738caad9bd19 {i U : ℕ} (hU : 1 ≤ U) (hi : U ≤ i) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖(((i + 1 : ℕ) : ℂ) ^ (-w) - (i : ℂ) ^ (-w))‖ ≤ ‖w‖ / U := by sorry

alias «Formalism».«HermitianLattices».«Ext».«PrimesInProgressions».«Dens».«norm_cpow_step_le'» := P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_norm_cpow_step_le__738caad9bd19
