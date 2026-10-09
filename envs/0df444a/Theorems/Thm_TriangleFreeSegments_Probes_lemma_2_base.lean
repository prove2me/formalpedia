-- Prove2me | Theorems.Thm_TriangleFreeSegments_Probes_lemma_2_base
-- name    : TriangleFreeSegments.Probes.lemma_2_base
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:16.071037+00:00
-- url     : https://prove2.me/theorems/c953d1aa-b490-4b9e-b180-35fc68828dec
-- title:
--   Proof of Lemma 2, p. 3 — base case k = 1: one segment and one probe in any rectangle of positive area
-- statement:
--   Let $R=[a,c]\times[b,d]$ be an axis-aligned rectangle with positive area, $a<c$ and $b<d$. Then there are a family $\mathcal S_1$ of $s_1=1$ line segment and a family $\mathcal P_1$ of $p_1=1$ probe such that $(\mathcal S_1,\mathcal P_1)$ is a probe system for $R$ with parameter $k=1$:
--   $$
--   \mathcal S_1\subseteq\operatorname{int}R\ \text{triangle-free},\quad \mathcal P_1\ \text{pairwise disjoint probes for }(\mathcal S_1,R),\quad \forall\phi\ \exists P\in\mathcal P_1:\ \phi\ \text{uses}\ \ge1\ \text{color on the segments meeting }P.
--   $$
--   Concretely, the segment is non-degenerate and lies in the interior of $R$, and every proper coloring uses at least one color on the segments meeting the probe, i.e. the probe meets the segment.
--
--   This is the base of the induction proving Lemma 2: the paper takes a non-horizontal segment inside $R$ and a thin probe reaching the right boundary of $R$ whose lower and upper boundaries cross the segment.
--
--   **Formalization Note** The conclusion is the predicate `ProbeSystem 1 R e pr` of the definitions file with $N=s_1$ and $M=p_1$, including non-degeneracy of the segment and the interior containment.
-- source:
--   Pawlik et al., Triangle-free intersection graphs of line segments with large chromatic number, arXiv:1209.1595v5, p. 3, proof of Lemma 2, base case k = 1

import Mathlib
import Definitions.Def_TriangleFreeSegments_Probes_Setting

namespace TriangleFreeSegments.Probes

theorem lemma_2_base (R : Rect) (hac : R.a < R.c) (hbd : R.b < R.d) :
    ∃ (e : Fin (sSeq 1) → (ℝ × ℝ) × (ℝ × ℝ)) (pr : Fin (pSeq 1) → ProbeData),
      ProbeSystem 1 R e pr := by sorry

end TriangleFreeSegments.Probes
