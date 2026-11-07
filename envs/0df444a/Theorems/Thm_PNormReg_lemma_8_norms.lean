-- Prove2me | Theorems.Thm_PNormReg_lemma_8_norms
-- name    : PNormReg.lemma_8_norms
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:04.141638+00:00
-- url     : https://prove2.me/theorems/4fc80376-849f-456a-8edf-e5bb1518ccfd
-- title:
--   Proof of Lemma 8, pp.24–25 — $\|M\|_{p,2}\le\sqrt{128d}$ and $\|c\|_p\le16d^{1/2-1/p}$, with every link of the chains
-- statement:
--   Let $A$ have full column rank with $k\le d$ columns, $D\succeq0$, $p\ge2$, $w$ Lewis weight overestimates of $A$, $s=\|w\|_1$, $\zeta>0$, $LL^\top=\bar D$, and $B=\bar AL^{-\top}$, $M=\rho B$, $c=-\tfrac12BL^{-1}\bar h$. Then:
--
--   1. $\bar D\succeq(8s)^{-(1-2/p)}\bar A^\top W^{1-2/p}\bar A$;
--   2. $\|W^{1/2-1/p}B\|_{2\to2}\le(8s)^{1/2-1/p}$ and $\|B\|_{2\to p}\le(8s)^{1/2-1/p}$;
--   3. $|(\bar Av)_i|\le w_i^{1/p}\|W^{1/2-1/p}\bar Av\|_2$ for all $v$, and $\|B_{i,:}\|_2\le w_i^{1/p}(8s)^{1/2-1/p}$;
--   4. $\|M\|_{p,2}\le\rho(8s)^{1/2-1/p}s^{1/p}\le8\sqrt s\le\sqrt{128d}$;
--   5. $\|c\|_p\le\tfrac12\|B\|_{2\to p}\|L^{-1}\bar h\|_2\le\tfrac12(8s)^{1/2-1/p}\sqrt{32}\le8s^{1/2-1/p}\le16d^{1/2-1/p}$.
--
--   These bounds fix the normalization $\Lambda=O(\sqrt d)$ of the games, which is what makes each game cost $\widetilde O_p(nd)$.
--
--   Differences from the source:
--   - generalization: D̄^{−1/2}, and φ⋆ ∈ (ζ/2, ζ] in the surrounding text → any L with LL⊤ = D̄, and every ζ > 0; reason: p.25: "The bounds above hold at every scale where a game is formed", and it covers the Cholesky factor; the printed choices are instances
--   - encoding: "the leverage-score calculation … applied to Ā" → w are overestimates of A, and the bounds are stated for Ā; reason: p.22 notes uniform scaling preserves leverage scores
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Proof of Lemma 8, norm bounds, pp.24–25 (PDF pp.25–26)

import Mathlib
import Definitions.Def_PNormReg_Scaled

open Matrix

namespace PNormReg

/-- **Proof of Lemma 8**, norm bounds, pp.24–25 (PDF pp.25–26).

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…).

For every `ζ > 0`, `k ≤ d` and `L` with `LL⊤ = D̄`, with `s = ∥w∥₁`, `B = ĀL^{−⊤}`, `M = ρB`,
`c = −½BL^{−1}h̄`:
* `D̄ ⪰ (8s)^{−(1−2/p)}Ā⊤W^{1−2/p}Ā`;
* `∥W^{1/2−1/p}B∥_{2→2} ≤ (8s)^{1/2−1/p}` and `∥B∥_{2→p} ≤ (8s)^{1/2−1/p}`;
* `|(Āv)_i| ≤ w_i^{1/p}∥W^{1/2−1/p}Āv∥₂` for every `v`, and `∥B_{i,:}∥₂ ≤ w_i^{1/p}(8s)^{1/2−1/p}`;
* `∥M∥_{p,2} ≤ ρ(8s)^{1/2−1/p}s^{1/p} ≤ 8√s ≤ √(128d)`;
* `∥c∥_p ≤ ½∥B∥_{2→p}∥L^{−1}h̄∥₂ ≤ ½(8s)^{1/2−1/p}√32 ≤ 8s^{1/2−1/p} ≤ 16d^{1/2−1/p}`.

**Formalization Note.** `w` are overestimates of `A`, and p.23 notes they are also overestimates of the
positive multiple `Ā`. `L` covers the printed `D̄^{1/2}` and the Cholesky factor of p.25. -/
theorem lemma_8_norms {n k : ℕ} (d : ℕ) (hk : k ≤ d) (A : Matrix (Fin n) (Fin k) ℝ)
    (hA : Function.Injective A.mulVec) (D : Matrix (Fin k) (Fin k) ℝ) (hD : D.PosSemidef)
    (h : Fin k → ℝ) (w : Fin n → ℝ) (p ζ : ℝ) (hp : 2 ≤ p) (hw : IsLewisOver A (1 / p) w)
    (hζ : 0 < ζ) (L : Matrix (Fin k) (Fin k) ℝ) (hL : L * Lᵀ = scaledD A D h w p ζ) :
    let s : ℝ := ∑ i, w i
    let hbar := scaledH h ζ
    let Abar := scaledA A p ζ
    let B : Matrix (Fin n) (Fin k) ℝ := Abar * (L⁻¹)ᵀ
    let e : ℝ := 1 / 2 - 1 / p
    let ρ : ℝ := rhoOf L hbar
    (scaledD A D h w p ζ - (8 * s) ^ (-(1 - 2 / p)) • weightedGram Abar w p).PosSemidef ∧
    opTwoTo 2 (weightedMat w e B) ≤ (8 * s) ^ e ∧
    opTwoTo p B ≤ (8 * s) ^ e ∧
    (∀ (v : Fin k → ℝ) (i : Fin n),
      |(Abar *ᵥ v) i| ≤ w i ^ (1 / p) * l2Norm (weightedMat w e Abar *ᵥ v)) ∧
    (∀ i : Fin n, l2Norm (B i) ≤ w i ^ (1 / p) * (8 * s) ^ e) ∧
    rowNormP2 p (gameM Abar L hbar) ≤ ρ * (8 * s) ^ e * s ^ (1 / p) ∧
    ρ * (8 * s) ^ e * s ^ (1 / p) ≤ 8 * Real.sqrt s ∧
    8 * Real.sqrt s ≤ Real.sqrt (128 * d) ∧
    lpNorm p (gameC Abar L hbar) ≤ (1 / 2) * opTwoTo p B * l2Norm (L⁻¹ *ᵥ hbar) ∧
    (1 / 2) * opTwoTo p B * l2Norm (L⁻¹ *ᵥ hbar) ≤ (1 / 2) * (8 * s) ^ e * Real.sqrt 32 ∧
    (1 / 2) * (8 * s) ^ e * Real.sqrt 32 ≤ 8 * s ^ e ∧
    8 * s ^ e ≤ 16 * (d : ℝ) ^ e := by sorry

end PNormReg
