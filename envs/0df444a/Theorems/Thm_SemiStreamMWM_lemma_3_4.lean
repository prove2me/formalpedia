-- Prove2me | Theorems.Thm_SemiStreamMWM_lemma_3_4
-- name    : SemiStreamMWM.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:27:46.02088+00:00
-- url     : https://prove2.me/theorems/e2d1f1fa-515b-415e-88f4-522233474796
-- title:
--   Lemma 3.4 — a crossing matching step of size at most $\delta/4$ keeps every odd-set constraint
-- statement:
--   Let $0<\delta<1$, $x\in\mathcal P_{G,\delta}$, and let $\mathcal Q$ be the partition of §3.1. For every crossing matching $J$ (no edge of $J$ has both endpoints in one part), every odd set $S\in\mathcal O_G$, and every $0\le\eta\le\delta/4$,
--
--   $$(x+\eta\vec1_J)(S)\le(|S|-1)/2.$$
--
--   This is property 2 of Lemma 3.1 (the odd-set guarantee) for the partition of §3.1; it lets Algorithm 2.1 add a crossing matching without leaving the matching polytope.
--
--   Differences from the source:
--   - generalization: δ = t log W ≤ 1/32 (the setting of every application) → every 0 < δ < 1; reason: the proof uses only γ ≤ δ²/16 and |S| > 1/δ ⇒ (1 − 2δ + η)|S|/2 < (|S| − 1)/2, valid for all such δ; it specializes to the paper's δ
--   - generalization: Q_v the (unique) inclusion-minimal minimum cut side → any choice of inclusion-minimal minimum cut sides; reason: uniqueness is not assumed; the statement covers the paper's choice
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), Lemma 3.4, p.15; §3.1 p.14

import Mathlib
import Definitions.Def_SemiStreamMWM_Graph
import Definitions.Def_SemiStreamMWM_CutPartition

open Classical

namespace SemiStreamMWM

/-- J. Chen (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), Lemma 3.4, p.15, for the
partition `Q` of §3.1 (p.14).

"For any crossing matching J, S ∈ O_G, and 0 ≤ η ≤ δ/4, (x + η1_J)(S) ≤ (|S| − 1)/2."

**Formalization Note.** This is property 2 of Lemma 3.1 (p.14) for the partition of §3.1, built from
the input `x ∈ P_{G,δ}`: `OddSetGuarantee G (partsOf Qf) δ x` says that for every matching `J` of
crossing edges, every odd vertex set `S` (singletons included) and every real `0 ≤ η ≤ δ/4`,
`(x + η1_J)(S) ≤ (|S| − 1)/2`. `η` here is any real in `[0, δ/4]`, not the step size. The statement
is posed for every `0 < δ < 1`. -/
theorem lemma_3_4 {V : Type} [Fintype V] (G : SimpleGraph V) (δ : ℝ) (x : G.edgeSet → ℝ)
    (Qf : V → Finset V) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hx : x ∈ truncPolytope G δ)
    (hQ : ∀ v, IsMinimalMinCutSide G δ x v (Qf v)) :
    OddSetGuarantee G (partsOf Qf) δ x := by sorry

end SemiStreamMWM
