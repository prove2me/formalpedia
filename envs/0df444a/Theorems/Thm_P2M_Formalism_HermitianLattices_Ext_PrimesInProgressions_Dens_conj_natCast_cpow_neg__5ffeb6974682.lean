-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_conj_natCast_cpow_neg__5ffeb6974682
-- name    : P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_conj_natCast_cpow_neg__5ffeb6974682
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:54:26.768934+00:00
-- url     : https://prove2.me/theorems/54321a9b-6e38-4df6-a775-4191e161ad61
-- title:
--   P2 M Formalism Hermitian Lattices Ext Primes In Progressions Dens conj nat Cast cpow neg  5ffeb6974682: P2 M Formalism Hermitian Lattices Ext Primes In Progressions Dens conj nat Cast cpow neg  5ffeb6
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext Primes In Progressions Dens conj nat Cast cpow neg  5ffeb6974682 construction uses the P2 M Formalism Hermitian Lattices Ext Primes In Progressions Dens conj nat Cast cpow neg  5ffeb6974682 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensBlock.lean#L158-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensBlock.lean#L158-L162

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensDiv
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSpace
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensBlock
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

theorem P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_conj_natCast_cpow_neg__5ffeb6974682 (n : ℕ) (z : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (-z)) = (n : ℂ) ^ (-(starRingEnd ℂ) z) := by sorry

alias «Formalism».«HermitianLattices».«Ext».«PrimesInProgressions».«Dens».«conj_natCast_cpow_neg'» := P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_conj_natCast_cpow_neg__5ffeb6974682
