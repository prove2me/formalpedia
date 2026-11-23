-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_fourier_conv
-- name    : ReciprocityTheory.PGsh.L2.fourier_conv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:29.127667+00:00
-- url     : https://prove2.me/theorems/86e49cc7-009d-4599-befe-4c2f09e58de4
-- title:
--   L2: fourier conv
-- statement:
--   The L2 construction uses the fourier conv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationFourierLeOne.lean#L29-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationFourierLeOne.lean#L29-L43

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
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

theorem ReciprocityTheory.PGsh.L2.fourier_conv {H : Type} (χ : H → AddChar N C) (u w : N → C) (h : H) :
    fourier (R := R) (fun h a => χ h a) (conv u w) h =
      fourier (R := R) (fun h a => χ h a) u h * fourier (R := R) (fun h a => χ h a) w h := by sorry
