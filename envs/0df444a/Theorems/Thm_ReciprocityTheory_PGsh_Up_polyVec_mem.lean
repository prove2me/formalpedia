-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_polyVec_mem
-- name    : ReciprocityTheory.PGsh.Up.polyVec_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:50.419428+00:00
-- url     : https://prove2.me/theorems/5151dbb9-a479-4363-8069-3466515e886f
-- title:
--   Up: poly Vec mem
-- statement:
--   The Up construction uses the poly Vec mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLatInvMulVec.lean#L46-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLatInvMulVec.lean#L46-L60

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsUnitMinor
import Definitions.Def_ReciprocityTheory_DualLattices_SumLatInvMulVec
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
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {v : Valuation C NNReal}

theorem ReciprocityTheory.PGsh.Up.polyVec_mem {n h : ℕ} {a : Fin n → C} (F : Lat v (Fin n × Fin h))
    (hF : F.B = freeMat a h) (p : Polynomial C) (hp : ∀ k, v (p.coeff k) ≤ 1)
    (hdeg : p.natDegree < n) (u : Fin h → C) (hu : ∀ l, v (u l) ≤ 1) :
    (fun y : Fin n × Fin h => p.eval (a y.1) * u y.2) ∈ F.pts := by sorry
