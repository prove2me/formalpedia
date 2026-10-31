-- Prove2me | Theorems.Thm_ProphetMatchingEFGT_eq_13
-- name    : ProphetMatchingEFGT.eq_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:37.811492+00:00
-- url     : https://prove2.me/theorems/66a348dc-3633-426a-b9e3-4a14bc92c68d
-- title:
--   Eq. (13) — product lower bound on $\Pr[u,v\text{ have witnesses}]$
-- statement:
--   Let $0\le c$, $x\in\mathcal F_M$, and let the edges of a duplicate-free list arrive before $e=(uv)$, which is not in the list; assume Algorithm 3 is well defined on them. Let $\widetilde E$ be the active set, and let $\pi_u,\pi_v$ be the candidate samplers, with independent resamplings. Then
--   $$\Pr[u,v\text{ have witnesses}]\ \ge\sum_{\substack{u^*\ne v^*\\u^*,v^*\notin\{u,v\}}}\Pr_{\widetilde E,\pi_u,\pi_v}\Big[u^*\text{ cand. of }u,\ v^*\text{ cand. of }v,\ |\widetilde E\cap E_{u^*}|=|\widetilde E\cap E_{v^*}|=1\Big]$$
--   and the right side equals
--   $$\sum_{\substack{u^*\ne v^*\\u^*,v^*\notin\{u,v\}}}\Pr\big[u^*\text{ cand. of }u,\ (uv^*)\notin\widetilde E\big]\cdot\Pr\big[v^*\text{ cand. of }v,\ (vu^*)\notin\widetilde E\big]\cdot\Pr_{\widetilde E(G-\{u,v\})}\big[(su^*),(sv^*)\text{ not active }\forall s\in V\setminus\{u,v\}\big].$$
--
--   This factorization separates the contributions of $u$'s and $v$'s edges, which are disjoint once $(uv)$ is removed.
--
--   Differences from the source:
--   - encoding: probabilities of Algorithm 3 (realization of R and the coin with probability α) → probabilities in the active-edge process of p.14 (each earlier edge active independently with probability α_e x_e, active edges picked greedily in arrival order), computed as finite sums; reason: the page's own unification ('For the purpose of analysis…', p.14); same law whenever α_e ≤ 1
--   - encoding: Pr[u* candidate of u] · Pr[(uv*) ∉ Ẽ | u* candidate of u] (and the same for v) → product form Pr[A, B] ≥ c·Pr[B] (or the corresponding product of probabilities); reason: the conditional probability is undefined on null events (slip 6); equal where it is defined
--   - reading: the induction hypothesis 'α_e ≤ 1 for every edge e ∈ E but the last edge (uv)' (p.14), left implicit in the statement → hypothesis WellDefinedOn c x es: c ≤ Pr[both ends of e' unmatched at e'] for every earlier edge e'; reason: the statement is made inside this induction; the form c ≤ Pr[…] avoids the junk value α = c/0 = 0
--   - encoding: E with (uv) and the later edges removed (p.14), in the order σ → a duplicate-free list es of the edges arriving before e = (uv), e ∉ es; x_us := 0 when (us) is not in es; reason: an arrival order restricted to the prefix; x restricted to the prefix stays in FM
--   - encoding: x ∈ FM (§5, p.12) → InFM G x on the edges of the simple graph G; reason: same polytope (p.10)
--   - reading: c is Algorithm 3's constant → 0 ≤ c; reason: a selection probability; all values of §5 are positive
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, §5.3, eq. (13), p. 15

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_ActiveProcess

open Finset

namespace ProphetMatchingEFGT

/-- **Eq. (13), p. 15: the product lower bound on `Pr[u, v have witnesses]`.**
Ezra–Feldman–Gravin–Tang, arXiv:2002.09807v2, eq. (13), p. 15:
`Pr[u, v have witnesses] ≥ Σ_{u* ≠ v*; u*, v* ∉ {u,v}} Pr_{Ẽ,π_u,π_v}[u* candidate of u, v* candidate
of v, |Ẽ ∩ E_u*| = |Ẽ ∩ E_v*| = 1] = Σ_{u* ≠ v*; u*, v* ∉ {u,v}} Pr[u* candidate of u] ·
Pr[(uv*) ∉ Ẽ | u* candidate of u] × Pr[v* candidate of v] · Pr[(vu*) ∉ Ẽ | v* candidate of v] ×
Pr_{Ẽ(G−{u,v})}[(su*) and (sv*) not active ∀ s ∈ V ∖ {u, v}]`.

**Formalization Note.** Product form of the conditional probabilities:
`Pr[u* cand. of u] · Pr[(uv*) ∉ Ẽ | u* cand. of u] = Pr[u* cand. of u, (uv*) ∉ Ẽ]`. The patterns
`l` (= `Ẽ`), `l₁` (resampling of `π_u`) and `l₂` (resampling of `π_v`) are independent with the law of
the active-edge process of the edges `es` arriving before `e = (uv)`; Algorithm 3 is assumed well
defined on `es`. -/
theorem eq_13 {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : ℝ) (hc : 0 ≤ c) (x : Edge G → ℝ) (hx : InFM G x) (es : List (Edge G)) (hnd : es.Nodup)
    (e : Edge G) (he : e ∉ es) (u v : V) (huv : (e : Sym2 V) = s(u, v))
    (hwd : WellDefinedOn c x es) :
    (∑ a ∈ univ.filter (fun a => a ≠ u ∧ a ≠ v),
        ∑ b ∈ univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a),
          prob3 (actProbs c x es) (fun l l₁ l₂ => IsCandidate u l l₁ a ∧ IsCandidate v l l₂ b ∧
            activeDegree l a = 1 ∧ activeDegree l b = 1))
        ≤ prob (actProbs c x es) (fun l => HaveWitnesses l u v) ∧
      (∑ a ∈ univ.filter (fun a => a ≠ u ∧ a ≠ v),
        ∑ b ∈ univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a),
          prob3 (actProbs c x es) (fun l l₁ l₂ => IsCandidate u l l₁ a ∧ IsCandidate v l l₂ b ∧
            activeDegree l a = 1 ∧ activeDegree l b = 1))
        = ∑ a ∈ univ.filter (fun a => a ≠ u ∧ a ≠ v),
            ∑ b ∈ univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a),
              prob2 (actProbs c x es) (fun l l₁ => IsCandidate u l l₁ a ∧ ¬ isActive l u b) *
              prob2 (actProbs c x es) (fun l l₂ => IsCandidate v l l₂ b ∧ ¬ isActive l v a) *
              prob (actProbs c x es) (fun l => ∀ s : V, s ≠ u → s ≠ v →
                ¬ isActive l s a ∧ ¬ isActive l s b) := by sorry

end ProphetMatchingEFGT
