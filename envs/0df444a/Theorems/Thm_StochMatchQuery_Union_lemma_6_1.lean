-- Prove2me | Theorems.Thm_StochMatchQuery_Union_lemma_6_1
-- name    : StochMatchQuery.Union.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:12:24.392018+00:00
-- url     : https://prove2.me/theorems/834d1b67-988a-4004-9dfd-9d74a261e53c
-- title:
--   Lemma 6.1 — Matching the non-crucial edges
-- statement:
--   Let $G$ have nonnegative weights and nonuniform edge probabilities in $(0,1]$, with nonempty edge set. Let $x_e$ be its optimum marginal under a fixed selector, and let $Q,\mathcal Q$ come from Algorithm 1. Assume the complete setting of Lemma 6.1: $h,\beta\in(0,1/10]$, $K\ge1$, $0<b\le b_0(K)$, $x_e/p_e\le b$ on $N$; $(M,A)$ is independent of $(Q,\mathcal G_N)$; $M$ is a matching and $A$ avoids its matched vertices. Vertex and pair availability floors, capacity, the absolute covariance row bound and (6.6) all hold. Write $I_v,\pi_v,\pi_{uv},g_e,L_v,f_e$ for the quantities in §6.
--
--   There exists a measurable random matching $M_N$ on this same probability space such that in every outcome it is contained in $N\cap\mathcal Q$ and both endpoints of each edge belong to $A$, and
--   $$\mathbb E[w(M_N)]\ge(1-3h)\sum_{e\in N}w_ex_e.$$
--   No independence from the crucial realization is imposed on $A$; only the pairwise-block independence in the hypotheses is required.
--
--   Differences from the source:
--   - encoding: p is the minimum of the edge probabilities → the edge set is nonempty where its minimum is used; reason: the minimum in the source is undefined for an edgeless graph
--   - encoding: r ≥ 6/(κβ²p), where p is the minimum edge probability → 6/(κβ²pₑ) ≤ r for every edge; reason: on a nonempty finite edge set this is equivalent to the minimum-probability bound
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Lemma 6.1, PDF/printed p.24–25. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- lemma 6 1; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem lemma_6_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (p w : Edge G → ℝ)
    (hne : (Finset.univ : Realization G).Nonempty)
    (s : Selector G w) (r : ℕ) (N : Realization G) (actual : Ω → Realization G)
    (samples : Ω → Fin r → Realization G) (M : Ω → Realization G) (A : Ω → Finset V)
    (h beta K b : ℝ)
    (H : NonCrucialData G μ p w s r N actual samples M A h beta K b) : ∃ MN : Ω → Realization G,
    Measurable MN ∧ (∀ ω, IsMatching G (MN ω) ∧
      MN ω ⊆ N ∩ queriedRealization G s (actual ω) (samples ω) ∧
      ∀ e ∈ MN ω, ∀ v, v ∈ (e : Sym2 V) → v ∈ A ω) ∧
    mean μ (fun ω => weightOf w (MN ω)) ≥ (1-3*h)*W G p s N := by sorry

end
end StochMatchQuery.Union
