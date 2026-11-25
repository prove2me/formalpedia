-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums__e_eq_aef0d302bf7a
-- name    : P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums__e_eq_aef0d302bf7a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:52:14.781882+00:00
-- url     : https://prove2.me/theorems/7bb509ed-075e-4edd-94cf-1aa6b5ad6e60
-- title:
--   P2 M Formalism Hermitian Lattices Ext Primes In Progressions Dens Eta Partial Sums  e eq aef0d302bf7a: P2 M Formalism Hermitian Lattices Ext Primes In Progressions Dens Eta Partial Sums  e eq aef0d302
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext Primes In Progressions Dens Eta Partial Sums  e eq aef0d302bf7a construction uses the P2 M Formalism Hermitian Lattices Ext Primes In Progressions Dens Eta Partial Sums  e eq aef0d302bf7a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensLs.lean#L77-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensLs.lean#L77-L84

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLs
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

theorem P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums__e_eq_aef0d302bf7a (j : ZMod 2) :
    Φe j = (1 : DirichletCharacter ℂ 2) j - (if j = 0 then 1 else 0) := by sorry

alias «Formalism».«HermitianLattices».«Ext».«PrimesInProgressions».«Dens».«EtaPartialSums».«Φe_eq» := P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums__e_eq_aef0d302bf7a
