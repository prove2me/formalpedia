-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_norm_dterm_le__f583cacc7f6d
-- name    : P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_norm_dterm_le__f583cacc7f6d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:58.628677+00:00
-- url     : https://prove2.me/theorems/e34799aa-1342-4327-bc4a-d87074eb2dcf
-- title:
--   P2 M Formalism Hermitian Lattices Ext Primes In Progressions Dens Eta Partial Sums norm dterm le  f583cacc7f6d: P2 M Formalism Hermitian Lattices Ext Primes In Progressions Dens Eta Partial Sums norm
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext Primes In Progressions Dens Eta Partial Sums norm dterm le  f583cacc7f6d construction uses the P2 M Formalism Hermitian Lattices Ext Primes In Progressions Dens Eta Partial Sums norm dterm le  f583cacc7f6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensLsA.lean#L107-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensLsA.lean#L107-L112

import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
import Theorems.Thm_P2M_Formalism_FX_LFunctionPartialSum_norm_dterm_le__3de663e13059

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
open Formalism.FX.LFunctionPartialSum
variable (f : ℕ → ℂ)

theorem P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_norm_dterm_le__f583cacc7f6d {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖dterm f s n‖ ≤ B * (‖s‖ / s.re * ((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re))) := by sorry

alias «Formalism».«HermitianLattices».«Ext».«PrimesInProgressions».«Dens».«EtaPartialSums».«norm_dterm_le'» := P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_norm_dterm_le__f583cacc7f6d
