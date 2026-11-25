-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_pairing_fourier
-- name    : ReciprocityTheory.PGsh.L2.pairing_fourier
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:05:27.843442+00:00
-- url     : https://prove2.me/theorems/8432686c-0a96-525c-acb9-f48a1a76e5f0
-- title:
--   L2: pairing fourier
-- statement:
--   The L2 construction uses the pairing fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemDualLatMapFourier.lean#L172-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemDualLatMapFourier.lean#L172-L178

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Definitions.Def_ReciprocityTheory_DualLattices_CharTableIsUnit
import Definitions.Def_ReciprocityTheory_DualLattices_TransposeMulSelf
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLatMapFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem ReciprocityTheory.PGsh.L2.pairing_fourier (e : H ≃ AddChar N C) (w : H → C) (u : N → C) :
    ∑ h, w h * fourier (R := R) (fun h a => e h a) u h =
      ∑ a, fourier (R := R) (fun a h => e h a) w a * u a := by sorry
