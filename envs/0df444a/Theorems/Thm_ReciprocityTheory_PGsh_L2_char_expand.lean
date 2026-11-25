-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_char_expand
-- name    : ReciprocityTheory.PGsh.L2.char_expand
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:06:11.054844+00:00
-- url     : https://prove2.me/theorems/3a1f6c22-281b-58e7-aad6-a0f7ee6e66d4
-- title:
--   L2: char expand
-- statement:
--   The L2 construction uses the char expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemDualLatMapFourier.lean#L97-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemDualLatMapFourier.lean#L97-L111

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

theorem ReciprocityTheory.PGsh.L2.char_expand (e : H ≃ AddChar N C) (B : Matrix N N C) (hB : IsUnit B.det) (h : H) (a : N) :
    e h a = ∑ i, fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) h * B a i := by sorry
