-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_av_full
-- name    : ReciprocityTheory.PGsh.Up.av_full
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T17:14:30.721078+00:00
-- url     : https://prove2.me/theorems/42e6d55f-1cef-51ca-97e5-3a6ebad32ef2
-- title:
--   Up: av full
-- statement:
--   The Up construction uses the av full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LengthDegreeAbelianVariety.lean#L30-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LengthDegreeAbelianVariety.lean#L30-L63

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqMulLeProd
import Definitions.Def_ReciprocityTheory_DualLattices_CokernelsAgreeEquivariantly
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeOfFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeOfWdetFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
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
open ReciprocityTheory.PGsh.L2

theorem ReciprocityTheory.PGsh.Up.av_full (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R)
    (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m))
    (horth : ∀ i j, e i * e j = if i = j then e i else 0) (hσ : ∀ i, σ (e i) = e (π i))
    (hsT : (∑ i, H.ρ (e i)) + H.P = 1) (hPT : ∀ i, H.ρ (e i) * H.P = 0)
    (hsL : (∑ i, H.ρL (e i)) + H.PL = 1) (hPL : ∀ i, H.ρL (e i) * H.PL = 0)
    (w : Fin m) (hw : π w ≠ w) (d : ℕ)
    (hd : Nonempty (LinearMap.range (Matrix.mulVecLin (H.ρL (e (π w)))) ≃ₗ[R] (Fin d → R)))
    (hnt : ∃ c : C, 0 < v c ∧ v c < 1) (n : ℕ) (a : Fin n → C) (hinj : Function.Injective a)
    (hint : ∀ τ, v (a τ) ≤ 1) (s h : ℕ) (A : Fin n → Matrix (Fin s) (Fin h) C)
    (F : Lat v (Fin n × Fin h)) (M M' : Lat v (Fin n × Fin s)) (Mτ M'τ : Fin n → Lat v (Fin s))
    (hF : F.B = freeMat a h) (hA : ∀ τ, Function.Surjective (A τ).mulVec)
    (hM' : M'.pts = (fun w : Fin n × Fin h → C => fun y : Fin n × Fin s =>
        ∑ l, A y.1 y.2 l * w (y.1, l)) '' F.pts)
    (hMst : IsLaStable a M) (hMτ : ∀ τ, (Mτ τ).pts = projPts M.pts τ)
    (hM'τ : ∀ τ, (M'τ τ).pts = projPts M'.pts τ)
    (Nw : Type) [AddCommGroup Nw] [Module R Nw] (E : htCoker H (e w) (e (π w)) ≃ₗ[R] Nw)
    (cw : NNReal) (hNw : HasLen v R Nw cw) (hcw : cw ≤ colen M' M) :
    ((v (algebraMap R C (p : R)) : ℝ) ^ ((d : ℝ) / (p - 1))) ^ 2 * (v (discr a) : ℝ) ^ h ≤
      ((∏ τ, colen (M'τ τ) (Mτ τ) : NNReal) : ℝ) ^ 2 * (v (discr a) : ℝ) ^ s := by sorry
