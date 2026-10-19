-- Prove2me | Theorems.Thm_QTDecode_Parallel_lemma_4
-- name    : QTDecode.Parallel.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:02.107985+00:00
-- url     : https://prove2.me/theorems/a66ec29a-d2a0-47c0-905e-21052ede37e3
-- title:
--   Lemma 4, p. 8 — expander mixing lemma for connected Δ-regular bipartite multigraphs
-- statement:
--   Let $\mathcal G$ be a connected $\Delta$-regular bipartite multigraph on the vertex set $V_0\cup V_1$, and let $\lambda\ge0$ bound the absolute values of all adjacency eigenvalues of $\mathcal G$ other than $\pm\Delta$ (so $\lambda\ge\lambda(\mathcal G):=\max\{|\lambda_i|:\lambda_i\ne\pm\Delta\}$). For any $S\subseteq V_0$ and $T\subseteq V_1$, the number of edges between $S$ and $T$, counted with multiplicity, satisfies
--   $$|E(S,T)|\ \le\ \frac{\Delta}{|V_0|}\,|S|\,|T|+\lambda\sqrt{|S|\,|T|}.$$
--
--   This is the expander mixing lemma in the form used throughout the paper: in the double covers of the Cayley graphs $\mathrm{Cay}(G,A)$ and $\mathrm{Cay}(G,B)$ (Lemmas 11 and 16) and in the square graphs $\mathcal G^\square_0,\mathcal G^\square_1$ (Lemmas 10 and 15).
--
--   **Formalization Note** The graph is given by its biadjacency matrix $N\in\mathbb R^{V_0\times V_1}$ with non-negative entries (the edge multiplicities; non-negative real weights are allowed) and every row and column sum equal to $\Delta$. Connectedness and the eigenvalues refer to the adjacency matrix $\begin{pmatrix}0&N\\N^{\mathsf T}&0\end{pmatrix}$, which is symmetric, so its eigenvalues are genuine. $|E(S,T)|=\sum_{s\in S,t\in T}N_{st}$. The explicit hypothesis $\lambda\ge0$ reflects that $\lambda(\mathcal G)$ is a maximum of absolute values; without it a graph all of whose eigenvalues are $\pm\Delta$ (a single edge) would make the statement false.
-- source:
--   Leverrier and Zémor, Decoding quantum Tanner codes, arXiv:2208.05537v3, p. 8, Lemma 4 (λ(𝒢) defined on p. 7)

import Mathlib
import Definitions.Def_QTDecode_Parallel_Model

namespace QTDecode.Parallel

open QAlgorithms
open scoped Matrix

/-- Lemma 4 (expander mixing lemma), p. 8. A connected `Δ`-regular bipartite (multi)graph on
`V₀ ∪ V₁`, given by its biadjacency matrix `N` (entry `N s t` = number of edges `s — t`), whose
adjacency eigenvalues other than `±Δ` have absolute value at most `lam` (`λ(𝒢) ≤ lam`, p. 7):
for all `S ⊆ V₀`, `T ⊆ V₁`, `|E(S, T)| ≤ (Δ/|V₀|)|S||T| + lam √(|S||T|)`. -/
theorem lemma_4 {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (N : Matrix V W ℝ) (Δ : ℕ) (lam : ℝ)
    (hN : ∀ s t, 0 ≤ N s t)
    (hrow : ∀ s, ∑ t, N s t = Δ) (hcol : ∀ t, ∑ s, N s t = Δ)
    (hconn : adjConnected (Matrix.fromBlocks 0 N Nᵀ 0))
    (hlam0 : 0 ≤ lam)
    (hlam : ∀ k, |ascEigenvalues (Matrix.fromBlocks 0 N Nᵀ 0) k| ≠ (Δ : ℝ) →
      |ascEigenvalues (Matrix.fromBlocks 0 N Nᵀ 0) k| ≤ lam)
    (S : Finset V) (T : Finset W) :
    ∑ s ∈ S, ∑ t ∈ T, N s t ≤
      (Δ : ℝ) / Fintype.card V * S.card * T.card + lam * Real.sqrt (S.card * T.card) := by sorry

end QTDecode.Parallel
