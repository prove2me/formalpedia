-- Prove2me | Theorems.Thm_RandTensorIso_Smoothed_lemma_4_11
-- name    : RandTensorIso.Smoothed.lemma_4_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:36:54.890243+00:00
-- url     : https://prove2.me/theorems/9fc97b38-2dbc-4749-b30a-8697ee743198
-- title:
--   Lemma 4.11 (complex form, §4.4) — column deletion
-- statement:
--   Let $B$ be a complex $n\times p$ matrix with $n\ge p\ge2$. Fix $j\in[p]$, let $x_j$ be the $j$-th column of $B$ and $B^{(j)}$ the $n\times(p-1)$ matrix obtained by deleting it. Fix $i<p$. Let $u$ be a unit eigenvector of $B^*B$ for $\lambda=\sigma_i(B)^2$ and $\hat u$ a unit eigenvector of $(B^{(j)})^*B^{(j)}$ for $\mu=\sigma_i(B^{(j)})^2$. Then, with $\langle x,y\rangle=\sum_kx_k\overline{y_k}$,
--   $$|u_j|\,\big|\langle B^{(j)}\hat u,x_j\rangle\big|\le\sigma_i(B)^2-\sigma_{i+1}(B)^2 .$$
--   The paper states this for real $B$ with transposes and says in §4.4 (p. 59) that, with adjoints for transposes and this inner product, its proof applies verbatim; the complex form is what Theorem 4.12 uses.
--
--   **Formalization Note.** $p=q+1$; $i$ is 0-based (`i : Fin q`, so `sv B i.castSucc` is $\sigma_i(B)$ and `sv B i.succ` is $\sigma_{i+1}(B)$ in the paper's 1-based indexing).
--
--   Differences from the source:
--   - generalization: Lemma 4.11 for a real n × p matrix with transposes → complex n × p matrix with adjoints and ⟨x, y⟩ = Σ x_k ȳ_k, as §4.4 extends it; reason: §4.4 states that the proof applies verbatim; a real matrix is a complex one, real eigenvectors are complex eigenvectors, so it specializes to the printed real lemma
--   - encoding: i < p (1-based), σ_i the i-th largest singular value → i : Fin q with p = q + 1, 0-based sv; reason: index shift only
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), p. 57 (PDF 59), Lemma 4.11; p. 59 (PDF 61), §4.4 (complex case)

import Mathlib
import Definitions.Def_RandTensorIso_Smoothed_Spectral

open Matrix

namespace RandTensorIso.Smoothed

/-- Lemma 4.11 (p. 57), complex form (§4.4, p. 59: adjoints for transposes,
`⟨x, y⟩ = ∑_k x_k ȳ_k`). `B` is `n × p` with `n ≥ p ≥ 2`, written `p = q + 1`; `x_j` is column `j`,
`B^{(j)}` is `B` with column `j` deleted; `i` (0-based, `i < p − 1`) stands for the paper's
`i < p`. If `u` is a unit eigenvector of `B^*B` for `σ_i(B)²` and `û` a unit eigenvector of
`B^{(j)*}B^{(j)}` for `σ_i(B^{(j)})²`, then `|u_j| |⟨B^{(j)} û, x_j⟩| ≤ σ_i(B)² − σ_{i+1}(B)²`. -/
theorem lemma_4_11 (n q : ℕ) (B : Matrix (Fin n) (Fin (q + 1)) ℂ)
    (hnp : q + 1 ≤ n) (hp : 2 ≤ q + 1) (j : Fin (q + 1)) (i : Fin q)
    (u : Fin (q + 1) → ℂ) (hu1 : vecNorm u = 1)
    (hu : (Bᴴ * B) *ᵥ u = ((sv B i.castSucc ^ 2 : ℝ) : ℂ) • u)
    (uh : Fin q → ℂ) (huh1 : vecNorm uh = 1)
    (huh : ((B.submatrix id j.succAbove)ᴴ * B.submatrix id j.succAbove) *ᵥ uh =
      ((sv (B.submatrix id j.succAbove) i ^ 2 : ℝ) : ℂ) • uh) :
    ‖u j‖ * ‖∑ k : Fin n, (B.submatrix id j.succAbove *ᵥ uh) k * star (B k j)‖ ≤
      sv B i.castSucc ^ 2 - sv B i.succ ^ 2 := by sorry

end RandTensorIso.Smoothed
