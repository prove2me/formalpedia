-- Prove2me | Theorems.Thm_QEC_Coding_PuncturedReedMuller_systematicCoset_weight_add_logical_dvd
-- name    : QEC.Coding.PuncturedReedMuller.systematicCoset_weight_add_logical_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:04:42.11863+00:00
-- url     : https://prove2.me/theorems/30981cb5-2d33-4cf5-81c1-8cd51bad9436
-- title:
--   Punctured Reed Muller: systematic Coset weight add logical dvd
-- statement:
--   A systematic punctured coset has Ward divisibility after the logical
--   low-coordinate contribution is restored.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L2090-L2144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L2090-L2144

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller

theorem QEC.Coding.PuncturedReedMuller.systematicCoset_weight_add_logical_dvd {w r m nu : Nat}
    (h : Admissible w r m) (hdegree : nu * r < m)
    (logical : Word (ZMod 2) (LowPoint m w))
    {word : Word (ZMod 2) (KeptPoint m w)}
    (hcoset : word - systematicKeptLift h logical ∈
      (shortenedReedMullerCode r m w).carrier) :
    2 ^ nu ∣ HammingWeight word + HammingWeight logical := by sorry
