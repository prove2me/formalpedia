-- Prove2me | Theorems.Thm_SemiStreamMWM_lemma_3_2
-- name    : SemiStreamMWM.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:27:14.849191+00:00
-- url     : https://prove2.me/theorems/ca4d2fa5-2f0d-40ad-a999-0dfd877a5ec2
-- title:
--   Lemma 3.2 — the inclusion-minimal minimum cut sides form a laminar family
-- statement:
--   Let $0<\delta<1$ and $x\in\mathcal P_{G,\delta}$, and build the rooted graph $G_{\tilde x,\delta}$ of §3.1 with cut capacity $f$. For each vertex $v$ let $Q_v$ be an inclusion-minimal minimum $v$–$r$ cut side containing $v$. Then the family $\{Q_v:v\in V\}$ is **laminar**: for all $u,v$,
--
--   $$Q_u\subseteq Q_v\quad\text{or}\quad Q_v\subseteq Q_u\quad\text{or}\quad Q_u\cap Q_v=\emptyset.$$
--
--   Laminarity is what makes the inclusion-maximal sides a partition of $V$.
--
--   Differences from the source:
--   - generalization: δ = t log W with 0 < t ≤ 1/(32 log W) (so δ ≤ 1/32), the setting of every application → every 0 < δ < 1; reason: γ > 0 and all capacities are nonnegative for δ < 1, and the proof uses only submodularity and posimodularity of the cut function; it specializes to the paper's δ
--   - generalization: Q_v the (unique) inclusion-minimal minimum cut side → any choice of inclusion-minimal minimum cut sides Q_v; reason: uniqueness (asserted on p.14) is not assumed; the statement covers the paper's choice
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), Lemma 3.2, p.14; §3.1 p.14

import Mathlib
import Definitions.Def_SemiStreamMWM_Graph
import Definitions.Def_SemiStreamMWM_CutPartition

open Classical

namespace SemiStreamMWM

/-- J. Chen (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), Lemma 3.2, p.14, for the
construction of §3.1 (p.14).

"The family {Q_v : v ∈ V} is laminar: any two members are nested or disjoint."

**Formalization Note.** `Qf v` is any inclusion-minimal minimum `v–r` cut side containing `v` in the
rooted graph `G_{x̃,δ}` built from the input `x ∈ P_{G,δ}` of Lemma 3.1 (p.14 says this side is
unique; that is not assumed). The paper applies the construction with `δ = t log W ≤ 1/32`; the
statement is posed for every `0 < δ < 1`, where `γ > 0` and every capacity of `G_{x̃,δ}` is
nonnegative. -/
theorem lemma_3_2 {V : Type} [Fintype V] (G : SimpleGraph V) (δ : ℝ) (x : G.edgeSet → ℝ)
    (Qf : V → Finset V) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hx : x ∈ truncPolytope G δ)
    (hQ : ∀ v, IsMinimalMinCutSide G δ x v (Qf v)) :
    ∀ u v, Qf u ⊆ Qf v ∨ Qf v ⊆ Qf u ∨ Disjoint (Qf u) (Qf v) := by sorry

end SemiStreamMWM
