-- Prove2me | Theorems.Thm_WangKangXue_SpectralTuran_lemma_3_2
-- name    : WangKangXue.SpectralTuran.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:24:11.454548+00:00
-- url     : https://prove2.me/theorems/2252aa20-18dc-4fdd-9b25-dfb2342e8b4f
-- title:
--   Lemma 3.2 — λ(G) ≥ (1 − 1/r)n − r/(4n) + 2a/n
-- statement:
--   Let $r \ge 2$ and let $F$ be a graph whose extremal graphs are $T_{n,r}$ plus a fixed number $a$ of edges for all large $n$ (the standing hypothesis of Section 3). Then there is $N$ such that for every $n \ge N$ and every $n$-vertex $F$-free graph $G$ of maximum spectral radius,
--   $$
--   \lambda(G) \ \ge\ \Big(1 - \frac1r\Big)n - \frac{r}{4n} + \frac{2a}{n}.
--   $$
--
--   This lower bound feeds the spectral stability theorem (Corollary 2.6) and is used again in Lemmas 3.6 and 3.8.
--
--   **Formalization Note** The inequality is stated in $\mathbb R$ with $n$ cast to a real number.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, p. 4, Lemma 3.2

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad
import Definitions.Def_WangKangXue_SpectralTuran_IsSpectralExtremal
import Definitions.Def_WangKangXue_SpectralTuran_TuranPlusEdges

namespace WangKangXue.SpectralTuran

open Classical

/-- **Lemma 3.2** (Wang–Kang–Xue, arXiv:2203.10831v1, p. 4). Under the standing hypotheses of
Section 3, for all large `n` every `n`-vertex `F`-free graph `G` of maximum spectral radius
satisfies `λ(G) ≥ (1 − 1/r) n − r/(4n) + 2a/n`. -/
theorem lemma_3_2 {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (hF : TuranPlusEdges F r a) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      (1 - 1 / (r : ℝ)) * n - r / (4 * n) + 2 * a / n ≤ specRad G := by sorry

end WangKangXue.SpectralTuran
