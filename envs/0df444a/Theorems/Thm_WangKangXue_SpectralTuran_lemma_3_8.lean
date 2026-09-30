-- Prove2me | Theorems.Thm_WangKangXue_SpectralTuran_lemma_3_8
-- name    : WangKangXue.SpectralTuran.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:28:00.143454+00:00
-- url     : https://prove2.me/theorems/27751f47-7af9-4b60-bd75-63e729d64f33
-- title:
--   Lemma 3.8 — every Perron entry is at least 1 − 20a²r²/n (for a ≥ 1)
-- statement:
--   Let $r \ge 2$, $a \ge 1$, and let $F$ be a graph whose extremal graphs are $T_{n,r}$ plus $a$ edges for all large $n$ (the standing hypothesis of Section 3). There is $N$ such that for every $n \ge N$ and every $n$-vertex $F$-free graph $G$ of maximum spectral radius the following holds. Let $\mathbf x$ be a positive eigenvector of $A(G)$ for $\lambda(G)$, normalised so that $\max_{i} x_i = 1$. Then
--   $$
--   x_u \ \ge\ 1 - \frac{20a^2r^2}{n} \qquad \text{for every } u \in V(G).
--   $$
--
--   All Perron entries are thus within $O(1/n)$ of the maximum, which is what lets the final Rayleigh-quotient comparisons (Lemma 3.10 and the proof of Theorem 1.2) be carried out edge by edge.
--
--   **Formalization Note** The hypothesis $a \ge 1$ is **not** on the page, and it is needed: as printed, the lemma fails at $a = 0$. Take $F = K_{r+1}$, for which $a = 0$ and the spectral extremal graph is $T_{n,r}$ (Nikiforov); if $r \nmid n$, the normalised Perron vector of $T_{n,r}$ has entries $(\lambda + \lfloor n/r\rfloor)/(\lambda + \lceil n/r\rceil) < 1$ on the larger parts (paper, p. 14), while the printed bound is $1 - 0 = 1$. The last inequality of the proof on p. 12 also needs $a \ge 1$. The mission's goal theorem does not assume $a \ge 1$. The eigenvector is quantified universally: every vector $x$ with $A(G)x = \lambda(G)x$, all entries in $(0,1]$ and some entry equal to $1$.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, p. 11, Lemma 3.8 (x as fixed on p. 4)

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad
import Definitions.Def_WangKangXue_SpectralTuran_IsSpectralExtremal
import Definitions.Def_WangKangXue_SpectralTuran_TuranPlusEdges

namespace WangKangXue.SpectralTuran

open Classical

/-- **Lemma 3.8** (Wang–Kang–Xue, arXiv:2203.10831v1, p. 11), with the hypothesis `a ≥ 1` that
the printed statement omits (it is false at `a = 0`: take `F = K_{r+1}`, `G = T_{n,r}`, `r ∤ n`).
Under the standing hypotheses of Section 3, for all large `n`: if `G` is an `n`-vertex `F`-free
graph of maximum spectral radius and `x` is a positive eigenvector of `A(G)` for `λ(G)` with
`max_i x_i = 1`, then `x_u ≥ 1 − 20 a² r² / n` for every vertex `u`. -/
theorem lemma_3_8 {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (ha : 1 ≤ a) (hF : TuranPlusEdges F r a) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      ∀ x : Fin n → ℝ, (G.adjMatrix ℝ).mulVec x = specRad G • x →
        (∀ i, 0 < x i) → (∀ i, x i ≤ 1) → (∃ z, x z = 1) →
        ∀ u : Fin n, 1 - 20 * (a : ℝ) ^ 2 * (r : ℝ) ^ 2 / n ≤ x u := by sorry

end WangKangXue.SpectralTuran
