-- Prove2me | Theorems.Thm_WangKangXue_SpectralTuran_lemma_3_1
-- name    : WangKangXue.SpectralTuran.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:23:31.218788+00:00
-- url     : https://prove2.me/theorems/22846499-a777-47e8-aee4-fa2e392ce60e
-- title:
--   Lemma 3.1 — the spectral extremal graph is connected
-- statement:
--   Let $r \ge 2$ and let $F$ be a graph whose extremal graphs are $T_{n,r}$ plus a fixed number $a$ of edges for all large $n$ (the standing hypothesis of Section 3). Then there is $N$ such that for every $n \ge N$, every $n$-vertex $F$-free graph $G$ of maximum spectral radius among $n$-vertex $F$-free graphs is **connected**.
--
--   Connectivity is what makes the Perron eigenvector of $G$ positive and unique, which the remaining lemmas use.
--
--   **Formalization Note** Graphs are on the vertex type `Fin n`; "for $n$ large enough" is an explicit threshold $N$ chosen after $F$, $r$ and $a$ and before $G$.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, p. 4, Lemma 3.1

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad
import Definitions.Def_WangKangXue_SpectralTuran_IsSpectralExtremal
import Definitions.Def_WangKangXue_SpectralTuran_TuranPlusEdges

namespace WangKangXue.SpectralTuran

open Classical

/-- **Lemma 3.1** (Wang–Kang–Xue, arXiv:2203.10831v1, p. 4). Under the standing hypotheses of
Section 3, for all large `n` every `n`-vertex `F`-free graph of maximum spectral radius is
connected. -/
theorem lemma_3_1 {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (hF : TuranPlusEdges F r a) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G → G.Connected := by sorry

end WangKangXue.SpectralTuran
