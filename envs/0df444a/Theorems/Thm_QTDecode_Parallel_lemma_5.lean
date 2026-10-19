-- Prove2me | Theorems.Thm_QTDecode_Parallel_lemma_5
-- name    : QTDecode.Parallel.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:02.630831+00:00
-- url     : https://prove2.me/theorems/be77babb-dd6c-46ae-ad9e-b3053a449251
-- title:
--   Lemma 5, p. 10 — λ(𝒢□₀) ≤ 4Δ and λ(𝒢□₁) ≤ 4Δ for non-bipartite Ramanujan Cay(G, A), Cay(G, B)
-- statement:
--   Let $G$ be a finite group and $A=A^{-1}$, $B=B^{-1}\subseteq G$ with $|A|=|B|=\Delta$. Suppose that the left Cayley graph $\mathrm{Cay}(G,A)$ (edges $g\sim ag$) and the right Cayley graph $\mathrm{Cay}(G,B)$ (edges $g\sim gb$) are non-bipartite Ramanujan graphs: connected, with every adjacency eigenvalue other than $\pm\Delta$ of absolute value at most $2\sqrt{\Delta-1}$, and $-\Delta$ not an eigenvalue. Let $\mathcal G^\square_0$ be the multigraph on $V_{00}\cup V_{11}$ and $\mathcal G^\square_1$ the multigraph on $V_{01}\cup V_{10}$ that put one edge between two vertices for every square of the quadripartite left-right Cayley complex containing both; both are $\Delta^2$-regular. Then
--   $$\lambda(\mathcal G^\square_0)\le 4\Delta,\qquad \lambda(\mathcal G^\square_1)\le 4\Delta,$$
--   that is, every adjacency eigenvalue of $\mathcal G^\square_k$ whose absolute value differs from $\Delta^2$ has absolute value at most $4\Delta$.
--
--   Together with the expander mixing lemma this controls the number of squares between two sets of vertices of $V_0$ or of $V_1$, the key estimate behind Lemmas 10 and 15.
--
--   **Formalization Note** The page assumes only "Ramanujan"; non-bipartiteness is the standing choice of p. 10 ("non-bipartite Ramanujan graphs") and is needed: for a bipartite $\mathrm{Cay}(G,A)$ the product of the eigenvalue $-\Delta$ with a non-trivial eigenvalue of $\mathrm{Cay}(G,B)$ can exceed $4\Delta$ in absolute value. The vertex $(g,b)\in G\times\mathrm{Bool}$ of `squareGraphAdj A B k` is $(g,00)$/$(g,11)$ for $k=0$ and $(g,01)$/$(g,10)$ for $k=1$; the matrix is symmetric, so its eigenvalues are genuine.
-- source:
--   Leverrier and Zémor, Decoding quantum Tanner codes, arXiv:2208.05537v3, p. 10, Lemma 5 (non-bipartite: p. 10, §2.4)

import Mathlib
import Definitions.Def_QTDecode_Parallel_Model

namespace QTDecode.Parallel

open QAlgorithms

/-- Lemma 5, p. 10. If `Cay(G, A)` and `Cay(G, B)` (left and right Cayley graphs, `A = A⁻¹`,
`B = B⁻¹`, `|A| = |B| = Δ`) are non-bipartite Ramanujan graphs, then `λ(𝒢□₀) ≤ 4Δ` and
`λ(𝒢□₁) ≤ 4Δ`: every adjacency eigenvalue of `𝒢□_k` other than `±Δ²` has absolute value at most
`4Δ`. Non-bipartiteness is the standing choice of p. 10. -/
theorem lemma_5 {G : Type} [Group G] [Fintype G] [DecidableEq G] (A B : Finset G) (Δ : ℕ)
    (hA : A.card = Δ) (hB : B.card = Δ)
    (hAinv : ∀ a ∈ A, a⁻¹ ∈ A) (hBinv : ∀ b ∈ B, b⁻¹ ∈ B)
    (hRamA : IsRamanujanAdj (leftCayleyAdj A) Δ)
    (hnbA : ∀ k, ascEigenvalues (leftCayleyAdj A) k ≠ -(Δ : ℝ))
    (hRamB : IsRamanujanAdj (rightCayleyAdj B) Δ)
    (hnbB : ∀ k, ascEigenvalues (rightCayleyAdj B) k ≠ -(Δ : ℝ)) :
    ∀ (k : Bool) (l : Fin (Fintype.card (G × Bool))),
      |ascEigenvalues (squareGraphAdj A B k) l| ≠ ((Δ : ℝ) ^ 2) →
      |ascEigenvalues (squareGraphAdj A B k) l| ≤ 4 * Δ := by sorry

end QTDecode.Parallel
