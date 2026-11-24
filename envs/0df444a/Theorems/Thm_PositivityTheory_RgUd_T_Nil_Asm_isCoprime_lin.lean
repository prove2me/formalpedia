-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Asm_isCoprime_lin
-- name    : PositivityTheory.RgUd.T.Nil.Asm.isCoprime_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:02.600563+00:00
-- url     : https://prove2.me/theorems/9dbf4680-41d8-43e5-b9e0-7c4880b2c709
-- title:
--   Asm: is Coprime lin
-- statement:
--   The Asm construction uses the is Coprime lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/NilpotentHypotheses/AevalProdLinearFactors.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/NilpotentHypotheses/AevalProdLinearFactors.lean#L50-L58

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_NilpotentHypotheses_AevalProdLinearFactors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Asm
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.RgUd.T.Nil.Asm.isCoprime_lin (α β γ : ℂ) (h : β - γ * α ≠ 0) : IsCoprime (X - C α) (C β - C γ * X) := by sorry
