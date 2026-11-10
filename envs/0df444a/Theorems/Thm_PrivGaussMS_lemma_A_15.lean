-- Prove2me | Theorems.Thm_PrivGaussMS_lemma_A_15
-- name    : PrivGaussMS.lemma_A_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:10:56.668191+00:00
-- url     : https://prove2.me/theorems/7696849c-58d8-49ce-8b13-1c6cb5a96653
-- title:
--   Lemma A.15 — inverse quadratic forms of frame blocks: $v^TZ^TGZv\overset d=\chi^2_r/\chi^2_{n-r-p}$ and (9)
-- statement:
--   Let $r,p\ge1$, $n-1\ge r+p$, let $Z\in\mathbb R^{r\times p}$ be the first $r$ rows and $p$ columns of a uniform orthogonal matrix of order $n-1$, and $G=(I_r-ZZ^T)^{-1}$. For each fixed unit $v\in\mathbb R^p$,
--   $$v^TZ^TGZv\overset d=\frac{\chi^2_r}{\chi^2_{n-r-p}}\tag{8}$$
--   with independent numerator and denominator. For fixed $w\in\mathbb R^r$ and $t>0$, outside probability $2e^{-t}$,
--   $$|v^TZ^TGw|\le\sqrt{\frac{2t}{r}(w^TGw)(v^TZ^TGZv)(1+v^TZ^TGZv)}.\tag{9}$$
--   The ratio identity also holds for $Z^T$, with $r,p$ exchanged: for each unit $v\in\mathbb R^r$, $v^TZ(I_p-Z^TZ)^{-1}Z^Tv\overset d=\chi^2_p/\chi^2_{n-p-r}$.
--
--   Differences from the source:
--   - encoding: uniform orthogonal matrix of order n − 1 → the uniform (n−1) × (n−1) frame (Haar law); reason: a square frame is an orthogonal matrix
--   - encoding: χ²_r/χ²_{n−r−p} with independent numerator and denominator → the pushforward of χ²_r ⊗ χ²_{n−r−p} under (u, v) ↦ u/v; reason: definition of the ratio law
--   - encoding: 'outside probability 2e^{−t}' → the event where (9) fails has probability ≤ 2e^{−t}; reason: same statement
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), Lemma A.15, p.30, eqs. (8)–(9)

import Mathlib
import Definitions.Def_PrivGaussMS_Frames

open MeasureTheory ProbabilityTheory Matrix

namespace PrivGaussMS

/-- **Lemma A.15** (Inverse quadratic forms of frame blocks), Moayedi, Yassaee, Ebrahimi,
*Optimal Private Gaussian Multi-sampling*, STOC 2027 submission (manuscript sha256 1838c582…),
p.30, eqs. (8)–(9).

Let `r, p ≥ 1`, `n − 1 ≥ r + p`, `Z ∈ ℝ^{r×p}` the first `r` rows and `p` columns of a uniform
orthogonal matrix of order `n − 1`, and `G = (I_r − ZZᵀ)^{−1}`. For each fixed unit `v ∈ ℝ^p`,
`vᵀZᵀGZv =d χ²_r/χ²_{n−r−p}` with independent numerator and denominator (8); for fixed `w ∈ ℝ^r`
and `t > 0`, outside probability `2e^{−t}`,
`|vᵀZᵀGw| ≤ √((2t/r)(wᵀGw)(vᵀZᵀGZv)(1 + vᵀZᵀGZv))` (9). The ratio identity also holds for `Zᵀ`,
with `r, p` exchanged.

**Formalization Note.** The uniform orthogonal matrix of order `n − 1` is `uniformFrame (n−1) (n−1)`
(Haar measure on `O(n − 1)`). `χ²_h` is the law of a sum of `h` squared independent standard
Gaussians; "with independent numerator and denominator" is the product law. The exchanged
statement uses `G' = (I_p − ZᵀZ)^{−1}` and a unit `v ∈ ℝ^r`. -/
theorem lemma_A_15 (n r p : ℕ) (hr : 1 ≤ r) (hp : 1 ≤ p) (hn : r + p ≤ n - 1) :
    let blk : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ → Matrix (Fin r) (Fin p) ℝ :=
      fun O => (firstRows r O).submatrix id (Fin.castLE (by omega))
    let G : Matrix (Fin r) (Fin p) ℝ → Matrix (Fin r) (Fin r) ℝ := fun Z => (1 - Z * Zᵀ)⁻¹
    let quad : Matrix (Fin r) (Fin p) ℝ → (Fin p → ℝ) → ℝ :=
      fun Z v => v ⬝ᵥ ((Zᵀ * G Z * Z) *ᵥ v)
    (∀ v : Fin p → ℝ, v ⬝ᵥ v = 1 →
      (uniformFrame (n - 1) (n - 1)).map (fun O => quad (blk O) v) =
        ((chiSq r).prod (chiSq (n - r - p))).map fun u => u.1 / u.2) ∧
    (∀ v : Fin p → ℝ, v ⬝ᵥ v = 1 → ∀ w : Fin r → ℝ, ∀ t : ℝ, 0 < t →
      (uniformFrame (n - 1) (n - 1)).real {O |
        Real.sqrt ((2 * t / r) * (w ⬝ᵥ (G (blk O) *ᵥ w)) * quad (blk O) v *
          (1 + quad (blk O) v)) < |v ⬝ᵥ (((blk O)ᵀ * G (blk O)) *ᵥ w)|} ≤
        2 * Real.exp (-t)) ∧
    (∀ v : Fin r → ℝ, v ⬝ᵥ v = 1 →
      (uniformFrame (n - 1) (n - 1)).map
          (fun O => v ⬝ᵥ ((blk O * (1 - (blk O)ᵀ * blk O)⁻¹ * (blk O)ᵀ) *ᵥ v)) =
        ((chiSq p).prod (chiSq (n - p - r))).map fun u => u.1 / u.2) := by sorry

end PrivGaussMS
