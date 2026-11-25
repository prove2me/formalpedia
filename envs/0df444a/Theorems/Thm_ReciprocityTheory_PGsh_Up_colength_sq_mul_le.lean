-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_colength_sq_mul_le
-- name    : ReciprocityTheory.PGsh.Up.colength_sq_mul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:31.160953+00:00
-- url     : https://prove2.me/theorems/3975ecfb-6586-444f-bfc9-c0209de25385
-- title:
--   Up: colength sq mul le
-- statement:
--   The Up construction uses the colength sq mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqMulLe.lean#L66-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqMulLe.lean#L66-L316

import Definitions.Def_ReciprocityTheory_DualLattices_SumLatInvMulVec
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqMulLe
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

theorem ReciprocityTheory.PGsh.Up.colength_sq_mul_le {n : ℕ} (a : Fin n → C) (hinj : Function.Injective a) (ha : ∀ τ, v (a τ) ≤ 1)
    (s h : ℕ) (A : Fin n → Matrix (Fin s) (Fin h) C) (F : Lat v (Fin n × Fin h))
    (M' S : Lat v (Fin n × Fin s)) (Mτ : Fin n → Lat v (Fin s)) (hF : F.B = freeMat a h)
    (hM' : M'.pts = phiMap A '' F.pts)
    (hMτ : ∀ τ, (Mτ τ).pts = projPts M'.pts τ) (hS : S.pts = sumPts Mτ) :
    colen M' S ^ 2 * v (discr a) ^ h ≤ v (discr a) ^ (2 * s) := by sorry
