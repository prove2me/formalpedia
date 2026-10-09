-- Prove2me | Theorems.Thm_TriangleFreeSegments_Probes_lemma_2_step
-- name    : TriangleFreeSegments.Probes.lemma_2_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:20.929022+00:00
-- url     : https://prove2.me/theorems/cdca109b-544d-464c-8875-7e8bd66391f5
-- title:
--   Proof of Lemma 2, pp. 3–4 — induction step: Lemma 2 at k for every rectangle implies Lemma 2 at k + 1 for every rectangle
-- statement:
--   Let $k\ge1$. Suppose that Lemma 2 holds at $k$: for every axis-aligned rectangle $R$ with positive area there are a family of $s_k$ segments and a family of $p_k$ rectangles forming a probe system for $R$ with parameter $k$ (see the definitions file). Then Lemma 2 holds at $k+1$: for every axis-aligned rectangle $R$ with positive area there are a family $\mathcal S_{k+1}$ of
--   $$
--   s_{k+1}=(p_k+1)s_k+p_k^2
--   $$
--   segments and a family $\mathcal P_{k+1}$ of $p_{k+1}=2p_k^2$ rectangles forming a probe system for $R$ with parameter $k+1$: the segments are distinct, non-degenerate, lie in the interior of $R$ and have a triangle-free intersection graph; the rectangles are pairwise disjoint probes for $(\mathcal S_{k+1},R)$; and every proper coloring of $\mathcal S_{k+1}$ uses at least $k+1$ colors on the segments meeting some probe of $\mathcal P_{k+1}$.
--
--   This is the inductive step of Lemma 2. It contains the construction of the paper (copies of $\mathcal S_k$ in the roots of the probes, the diagonals, the lower and upper probes) together with the claims about it: the new rectangles are probes, they are pairwise disjoint, the new family is triangle-free, and the counts are $s_{k+1}$ and $p_{k+1}$.
--
--   **Formalization Note** The induction hypothesis is supplied for every rectangle of positive area, because the step applies it both to $R$ and to the roots of the probes.
-- source:
--   Pawlik et al., Triangle-free intersection graphs of line segments with large chromatic number, arXiv:1209.1595v5, pp. 3–4, proof of Lemma 2, induction step

import Mathlib
import Definitions.Def_TriangleFreeSegments_Probes_Setting

namespace TriangleFreeSegments.Probes

theorem lemma_2_step (k : ℕ) (hk : 1 ≤ k)
    (ih : ∀ R : Rect, R.a < R.c → R.b < R.d →
      ∃ (e : Fin (sSeq k) → (ℝ × ℝ) × (ℝ × ℝ)) (pr : Fin (pSeq k) → ProbeData),
        ProbeSystem k R e pr) :
    ∀ R : Rect, R.a < R.c → R.b < R.d →
      ∃ (e : Fin (sSeq (k + 1)) → (ℝ × ℝ) × (ℝ × ℝ)) (pr : Fin (pSeq (k + 1)) → ProbeData),
        ProbeSystem (k + 1) R e pr := by sorry

end TriangleFreeSegments.Probes
