-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_L2_fourier_apply__9ba6b889acde
-- name    : P2M_ReciprocityTheory_PGsh_L2_fourier_apply__9ba6b889acde
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:36.6178+00:00
-- url     : https://prove2.me/theorems/196ea6bc-aaff-4f4f-8fc7-7b3a7e3ddc8d
-- title:
--   P2 M Reciprocity Theory PGsh L2 fourier apply  9ba6b889acde: P2 M Reciprocity Theory PGsh L2 fourier apply  9ba6b889acde
-- statement:
--   The P2 M Reciprocity Theory PGsh L2 fourier apply  9ba6b889acde construction uses the P2 M Reciprocity Theory PGsh L2 fourier apply  9ba6b889acde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationFourierLeOne.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationFourierLeOne.lean#L12-L13

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

theorem P2M_ReciprocityTheory_PGsh_L2_fourier_apply__9ba6b889acde {X H : Type} [Fintype X] (e : H → X → C) (u : X → C) (h : H) :
    fourier (R := R) e u h = ∑ a, u a * e h a := by sorry

alias «ReciprocityTheory».«PGsh».«L2».«fourier_apply'» := P2M_ReciprocityTheory_PGsh_L2_fourier_apply__9ba6b889acde
