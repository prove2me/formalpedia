-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_colength_sq_mul_le_prod
-- name    : ReciprocityTheory.PGsh.Up.colength_sq_mul_le_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:09:44.200277+00:00
-- url     : https://prove2.me/theorems/eb75d337-f43b-583c-b263-9c19bb59c539
-- title:
--   Up: colength sq mul le prod
-- statement:
--   The Up construction uses the colength sq mul le prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqMulLeProd.lean#L57-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqMulLeProd.lean#L57-L89

import Definitions.Def_ReciprocityTheory_DualLattices_DiscriminantColengthStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqMulLeProd
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec

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
variable {C : Type} [Field C] {v : Valuation C NNReal}

theorem ReciprocityTheory.PGsh.Up.colength_sq_mul_le_prod (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type)
    [CommRing R] [Algebra R C] (hv : v.Integers R) (hnt : ∃ c : C, 0 < v c ∧ v c < 1)
    (n : ℕ) (a : Fin n → C) (hinj : Function.Injective a) (hint : ∀ τ, v (a τ) ≤ 1)
    (s h : ℕ) (A : Fin n → Matrix (Fin s) (Fin h) C) (F : Lat v (Fin n × Fin h))
    (M M' : Lat v (Fin n × Fin s)) (Mτ M'τ : Fin n → Lat v (Fin s)) (hF : F.B = freeMat a h)
    (hA : ∀ τ, Function.Surjective (A τ).mulVec)
    (hM' : M'.pts = (fun w : Fin n × Fin h → C => fun y : Fin n × Fin s =>
        ∑ l, A y.1 y.2 l * w (y.1, l)) '' F.pts)
    (hMst : IsLaStable a M) (hMτ : ∀ τ, (Mτ τ).pts = projPts M.pts τ)
    (hM'τ : ∀ τ, (M'τ τ).pts = projPts M'.pts τ) :
    colen M' M ^ 2 * v (discr a) ^ h ≤ (∏ τ, colen (M'τ τ) (Mτ τ)) ^ 2 * v (discr a) ^ s := by sorry
