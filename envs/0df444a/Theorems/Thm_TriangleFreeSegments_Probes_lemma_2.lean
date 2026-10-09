-- Prove2me | Theorems.Thm_TriangleFreeSegments_Probes_lemma_2
-- name    : TriangleFreeSegments.Probes.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:27.070761+00:00
-- url     : https://prove2.me/theorems/aa88fbf2-5e11-44a9-8f4a-5faa409dacb2
-- title:
--   Lemma 2, p. 3 — s_k triangle-free segments in R with p_k disjoint probes, one of which sees ≥ k colors under every proper coloring
-- statement:
--   Let $k\ge1$ and let $R=[a,c]\times[b,d]$ be an axis-aligned rectangle with positive area ($a<c$, $b<d$). Let $s_k,p_k$ be given by $s_1=p_1=1$, $s_{i+1}=(p_i+1)s_i+p_i^2$, $p_{i+1}=2p_i^2$. Then there are
--
--   1. a family $\mathcal S_k$ of exactly $s_k$ distinct non-degenerate line segments, all contained in the open interior of $R$, whose intersection graph is triangle-free, and
--   2. a family $\mathcal P_k$ of exactly $p_k$ pairwise disjoint probes for $(\mathcal S_k,R)$,
--
--   such that for every proper coloring $\phi$ of (the intersection graph of) $\mathcal S_k$ there is a probe $P\in\mathcal P_k$ with
--   $$
--   \bigl|\{\phi(\sigma):\sigma\in\mathcal S_k,\ \sigma\cap P\neq\emptyset\}\bigr|\ \ge\ k .
--   $$
--
--   Lemma 2 is the technical statement behind Theorem 1: adding the diagonals of the probes of $\mathcal P_k$ to $\mathcal S_k$ gives a triangle-free family of segments with chromatic number greater than $k$.
--
--   **Formalization Note** The conclusion is the predicate `ProbeSystem k R e pr` of the definitions file, with $e$ indexed by `Fin (sSeq k)` and the probes by `Fin (pSeq k)`. "A family of $s_k$ line segments" is read as $s_k$ distinct segments, each with two distinct endpoints; probes are pairwise disjoint as closed rectangles; colors range over an arbitrary type.
-- source:
--   Pawlik et al., Triangle-free intersection graphs of line segments with large chromatic number, arXiv:1209.1595v5, p. 3, Lemma 2

import Mathlib
import Definitions.Def_TriangleFreeSegments_Probes_Setting

namespace TriangleFreeSegments.Probes

theorem lemma_2 (k : ℕ) (hk : 1 ≤ k) (R : Rect) (hac : R.a < R.c) (hbd : R.b < R.d) :
    ∃ (e : Fin (sSeq k) → (ℝ × ℝ) × (ℝ × ℝ)) (pr : Fin (pSeq k) → ProbeData),
      ProbeSystem k R e pr := by sorry

end TriangleFreeSegments.Probes
