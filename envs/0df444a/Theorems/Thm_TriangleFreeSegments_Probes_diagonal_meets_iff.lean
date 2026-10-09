-- Prove2me | Theorems.Thm_TriangleFreeSegments_Probes_diagonal_meets_iff
-- name    : TriangleFreeSegments.Probes.diagonal_meets_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:46.326772+00:00
-- url     : https://prove2.me/theorems/c3fc0830-47a2-44f0-b9ee-642a0e67b4ad
-- title:
--   Proof of Lemma 2, p. 3 — the diagonal D_Q of a probe crosses exactly the segments that meet the probe
-- statement:
--   Let $R=[a,c]\times[b,d]$ be a rectangle and $\mathcal S=(\sigma_i)_{i\in\iota}$ a family of closed line segments, each contained in the open interior $(a,c)\times(b,d)$ of $R$. Let $Q=[a',c]\times[b',d']$ be a probe for $(\mathcal S,R)$, that is, conditions (i)–(iv) hold: $a<a'<c$, $b<b'<d'<d$; no segment meets the left boundary $\{a'\}\times[b',d']$; no segment has an endpoint in $Q$; segments meeting $Q$ are pairwise disjoint. Let $D_Q$ be the diagonal of $Q$, from $(a',b')$ to $(c,d')$. Then for every $i$,
--   $$
--   \sigma_i\cap D_Q\neq\emptyset \iff \sigma_i\cap Q\neq\emptyset .
--   $$
--   In the paper's words: $D_Q$ crosses all segments pierced by $Q$ and no other segment. This is what makes the diagonal of a probe adjacent, in the intersection graph, to precisely the independent set of segments that the probe meets; it is used in the induction step of Lemma 2 and for the family $\tilde{\mathcal S}_k$.
--
--   **Formalization Note** On the page the claim is made for a probe $Q\in\mathcal Q_P$ of the copy $\mathcal S_P$ placed inside the root of $P$, and the segments are those of $\mathcal S_P$. Here it is stated for any probe of any segment family lying in the interior of a rectangle, which is the property the sentence relies on; the hypothesis that the segments lie in the open interior of $R$ is needed (otherwise a segment could cut only the bottom-right corner of $Q$ through its right edge).
-- source:
--   Pawlik et al., Triangle-free intersection graphs of line segments with large chromatic number, arXiv:1209.1595v5, p. 3, proof of Lemma 2, induction step: "Note that D_Q crosses all segments pierced by Q and no other segment."

import Mathlib
import Definitions.Def_TriangleFreeSegments_Probes_Setting

namespace TriangleFreeSegments.Probes

theorem diagonal_meets_iff {ι : Type} (e : ι → (ℝ × ℝ) × (ℝ × ℝ)) (R : Rect)
    (hin : ∀ i, seg (e i) ⊆ R.inner) (P : ProbeData) (hP : IsProbe e R P) (i : ι) :
    (seg (e i) ∩ seg (diag R P)).Nonempty ↔ (seg (e i) ∩ probeRect R P).Nonempty := by sorry

end TriangleFreeSegments.Probes
