-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_intervalIntegrable_inv_log__5efe15a227a2
-- name    : P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_intervalIntegrable_inv_log__5efe15a227a2
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:41.065277+00:00
-- url     : https://prove2.me/theorems/5796f422-6543-4fad-8f73-7408590cbdd1
-- title:
--   P2 M Formalism Hermitian Lattices Ext Primes In Progressions interval Integrable inv log  5efe15a227a2: P2 M Formalism Hermitian Lattices Ext Primes In Progressions interval Integrable inv log  5efe15
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext Primes In Progressions interval Integrable inv log  5efe15a227a2 construction uses the P2 M Formalism Hermitian Lattices Ext Primes In Progressions interval Integrable inv log  5efe15a227a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean#L68-L75

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_intervalIntegrable_inv_log__5efe15a227a2 {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume a b := by sorry

alias «Formalism».«HermitianLattices».«Ext».«PrimesInProgressions».«intervalIntegrable_inv_log'» := P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_intervalIntegrable_inv_log__5efe15a227a2
