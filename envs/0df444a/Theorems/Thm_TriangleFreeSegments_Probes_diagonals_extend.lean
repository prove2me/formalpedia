-- Prove2me | Theorems.Thm_TriangleFreeSegments_Probes_diagonals_extend
-- name    : TriangleFreeSegments.Probes.diagonals_extend
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:06.474113+00:00
-- url     : https://prove2.me/theorems/569246d7-7744-4a8c-906b-20df77f98a9e
-- title:
--   p. 4 — adding the diagonals of all probes to a probe system for k gives a triangle-free family with χ > k
-- statement:
--   Let $k\ge1$ and let $R$ be a rectangle. Let $\mathcal S=(\sigma_i)_{i<N}$ be a family of segments and $(P_j)_{j<M}$ a family of rectangles forming a probe system for $R$ with parameter $k$ (the conclusion of Lemma 2): distinct non-degenerate segments in the interior of $R$ with triangle-free intersection graph, pairwise disjoint probes for $(\mathcal S,R)$, and every proper coloring of $\mathcal S$ uses at least $k$ colors on the segments meeting some probe. Let $\tilde{\mathcal S}$ be the family indexed by the disjoint union of $\{0,\dots,N-1\}$ and $\{0,\dots,M-1\}$ consisting of the segments $\sigma_i$ and the diagonals $D_{P_j}$ of the probes. Then the intersection graph of $\tilde{\mathcal S}$ is triangle-free and
--   $$
--   \chi(\tilde{\mathcal S})>k .
--   $$
--
--   Applied to the family $\mathcal S_k$ and the probes $\mathcal P_k$ of Lemma 2, this is the paper's family $\tilde{\mathcal S}_k$, and it yields Theorem 1.
--
--   **Formalization Note** The page argues about "the family $\mathcal S_k$ constructed above"; its argument uses only the conclusion of Lemma 2, so the statement takes any data with that conclusion. The chromatic number is Mathlib's `chromaticNumber` with values in $\mathbb N\cup\{\infty\}$.
-- source:
--   Pawlik et al., Triangle-free intersection graphs of line segments with large chromatic number, arXiv:1209.1595v5, p. 4, paragraph after the proof of Lemma 2 (the family S̃_k)

import Mathlib
import Definitions.Def_TriangleFreeSegments_Probes_Setting

namespace TriangleFreeSegments.Probes

theorem diagonals_extend (k : ℕ) (hk : 1 ≤ k) (R : Rect) {N M : ℕ}
    (e : Fin N → (ℝ × ℝ) × (ℝ × ℝ)) (pr : Fin M → ProbeData) (h : ProbeSystem k R e pr) :
    let F : Fin N ⊕ Fin M → Set (ℝ × ℝ) :=
      Sum.elim (fun i => seg (e i)) (fun j => seg (diag R (pr j)))
    (interGraph F).CliqueFree 3 ∧ (k : ℕ∞) < (interGraph F).chromaticNumber := by sorry

end TriangleFreeSegments.Probes
