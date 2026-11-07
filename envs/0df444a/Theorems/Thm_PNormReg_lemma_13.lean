-- Prove2me | Theorems.Thm_PNormReg_lemma_13
-- name    : PNormReg.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:40:41.036096+00:00
-- url     : https://prove2.me/theorems/9b253da1-51dd-413c-a12c-a6e403c36cc2
-- title:
--   Lemma 13, p.24 — $\rho=\tfrac12\sqrt{\|\bar D^{-1/2}\bar h\|_2^2-1/2}\le3$, with $\|\bar D^{-1/2}\bar h\|_2^2\le32$
-- statement:
--   Let $\bar h,\bar D$ be as defined in Lemma 10, at any scale $\zeta>0$, and let $LL^\top=\bar D$. Then
--
--   $$\|L^{-1}\bar h\|_2^2\le32\qquad\text{and}\qquad\rho=\tfrac12\sqrt{\|L^{-1}\bar h\|_2^2-1/2}\le3.$$
--
--   It bounds the scalar in the game matrix, so that the matrix norm is controlled by the Lewis weight term alone.
--
--   Differences from the source:
--   - generalization: "as defined in Lemma 10", possibly with φ⋆ ∈ (ζ/2, ζ], and D̄^{−1/2} → every ζ > 0, and any L with LL⊤ = D̄; reason: the scale is not used by the proof, and p.25 says the bounds hold "at every scale where a game is formed"; the printed statement is an instance
--   - encoding: ρ ≤ 3 → also the bound ∥L⁻¹h̄∥₂² ≤ 32 from the proof, as a conjunct; reason: Real.sqrt of a negative number is 0, so the bound on the radicand keeps the claim meaningful
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Lemma 13 and its proof, p.24 (PDF p.25)

import Mathlib
import Definitions.Def_PNormReg_Scaled

open Matrix

namespace PNormReg

/-- **Lemma 13**, p.24 (PDF p.25), with the bound of its proof.

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…).

For every `ζ > 0` and `L` with `LL⊤ = D̄`: `∥L^{−1}h̄∥₂² ≤ 32` and `ρ = ½√(∥L^{−1}h̄∥₂² − 1/2) ≤ 3`.

**Formalization Note.** `Real.sqrt` of a negative number is `0`, so the bound `≤ 32` from the proof is a
conjunct. The scale hypothesis of Lemma 10 is not used: p.25 says the bounds hold "at every scale where
a game is formed". -/
theorem lemma_13 {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (hA : Function.Injective A.mulVec)
    (D : Matrix (Fin k) (Fin k) ℝ) (hD : D.PosSemidef) (h : Fin k → ℝ) (w : Fin n → ℝ) (p ζ : ℝ)
    (hp : 2 ≤ p) (hw : IsLewisOver A (1 / p) w) (hζ : 0 < ζ) (L : Matrix (Fin k) (Fin k) ℝ)
    (hL : L * Lᵀ = scaledD A D h w p ζ) :
    l2Norm (L⁻¹ *ᵥ scaledH h ζ) ^ 2 ≤ 32 ∧ rhoOf L (scaledH h ζ) ≤ 3 := by sorry

end PNormReg
