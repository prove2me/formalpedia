-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_dualLen_fin
-- name    : ReciprocityTheory.PGsh.Up.dualLen_fin
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:06:38.867887+00:00
-- url     : https://prove2.me/theorems/84e0edba-e94f-4f6d-857a-bf71d55fed8d
-- title:
--   Up: dual Len fin
-- statement:
--   The Up construction uses the dual Len fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MatEquivApply.lean#L41-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MatEquivApply.lean#L41-L165

import Definitions.Def_ReciprocityTheory_DualLattices_DualLenStatement
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R]

theorem ReciprocityTheory.PGsh.Up.dualLen_fin {C : Type} [Field C] {v : Valuation C NNReal} [Algebra R C]
    (hv : v.Integers R) {d n : ℕ} (A : Matrix (Fin d) (Fin n) R) (c : R) (hc : c ≠ 0)
    (hkill : ∀ w : Fin d → R, ∃ t, A *ᵥ t = c • w) {c₁ : NNReal}
    (hc₁ : HasLen v R ((Fin d → R) ⧸ LinearMap.range A.mulVecLin) c₁) :
    ∃ y : NNReal, HasLen v R ((Fin d → R) ⧸ zSub A c) y ∧ y * c₁ = v (algebraMap R C c) ^ d := by sorry
