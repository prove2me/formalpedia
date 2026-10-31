-- Prove2me | Theorems.Thm_ProphetMatchingEFGT_eq_15
-- name    : ProphetMatchingEFGT.eq_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:58.900712+00:00
-- url     : https://prove2.me/theorems/655e437d-354f-4b40-b204-619335b97d72
-- title:
--   Eq. (15) — the explicit lower bound $f(x)$ on $\Pr[u,v\text{ unmatched at }(uv)]$
-- statement:
--   Let $0<c<\tfrac12$, $x\in\mathcal F_M$, and let the edges of a duplicate-free list arrive before $e=(uv)$, which is not in the list; assume Algorithm 3 is well defined on them. With all sums over $s\in V\setminus\{u,v\}$ (and $x_{us}=0$ when $(us)$ is not an earlier edge),
--   $$\Pr_{\widetilde E}[u,v\text{ unmatched at }(uv)]\ \ge\ 1-c\Big(\sum_sx_{us}+\sum_sx_{vs}\Big)+\Pr_{\widetilde E}[u,v\text{ have witnesses}]$$
--   $$\ge\ 1-c\Big(\sum_sx_{us}+\sum_sx_{vs}\Big)+c^2\Big(\frac{1-2c}{1-c}\Big)^2\Big(\sum_sx_{us}\cdot\sum_sx_{vs}-\sum_sx_{us}x_{vs}\Big).$$
--
--   The right side is the function $f(x)$ minimized in Lemma 5.6.
--
--   Differences from the source:
--   - encoding: probabilities of Algorithm 3 (realization of R and the coin with probability α) → probabilities in the active-edge process of p.14 (each earlier edge active independently with probability α_e x_e, active edges picked greedily in arrival order), computed as finite sums; reason: the page's own unification ('For the purpose of analysis…', p.14); same law whenever α_e ≤ 1
--   - reading: the induction hypothesis 'α_e ≤ 1 for every edge e ∈ E but the last edge (uv)' (p.14), left implicit in the statement → hypothesis WellDefinedOn c x es: c ≤ Pr[both ends of e' unmatched at e'] for every earlier edge e'; reason: the statement is made inside this induction; the form c ≤ Pr[…] avoids the junk value α = c/0 = 0
--   - encoding: E with (uv) and the later edges removed (p.14), in the order σ → a duplicate-free list es of the edges arriving before e = (uv), e ∉ es; x_us := 0 when (us) is not in es; reason: an arrival order restricted to the prefix; x restricted to the prefix stays in FM
--   - reading: c is Algorithm 3's constant (1/3 or 0.337 in §5) → 0 < c < 1/2; reason: the denominators 1 − c − cΣ ≥ 1 − 2c and (1 − 2c)/(1 − c) of §5.3 presuppose c < 1/2
--   - encoding: x ∈ FM (§5, p.12) → InFM G x on the edges of the simple graph G; reason: same polytope (p.10)
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, §5.3, eq. (15), p. 16

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_ActiveProcess

open Finset

namespace ProphetMatchingEFGT

/-- **Eq. (15), p. 16.**
Ezra–Feldman–Gravin–Tang, arXiv:2002.09807v2, eq. (15), p. 16:
`Pr_Ẽ[u, v are unmatched at (uv)] ≥ 1 − c (Σ_s x_us + Σ_s x_vs) + Pr_Ẽ[u, v have witnesses]
≥ 1 − c (Σ_s x_us + Σ_s x_vs) + c² · ((1 − 2c)/(1 − c))² · (Σ_s x_us · Σ_s x_vs − Σ_s x_us · x_vs)`,
"where all summations are taken over `s ∈ V ∖ {u, v}`".

**Formalization Note.** The active-edge process of Algorithm 3 with constant `c ∈ (0, 1/2)` on the
edges `es` arriving before `e = (uv)`, assumed well defined on `es`; `x_us = 0` when `(us)` is not an
edge of `es`. -/
theorem eq_15 {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : ℝ) (hc0 : 0 < c) (hc : c < 1 / 2) (x : Edge G → ℝ) (hx : InFM G x)
    (es : List (Edge G)) (hnd : es.Nodup) (e : Edge G) (he : e ∉ es) (u v : V)
    (huv : (e : Sym2 V) = s(u, v)) (hwd : WellDefinedOn c x es) :
    1 - c * (∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s
        + ∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es v s)
        + prob (actProbs c x es) (fun l => HaveWitnesses l u v) ≤ unmatchedAt c x es e ∧
      1 - c * (∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s
          + ∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es v s)
        + c ^ 2 * ((1 - 2 * c) / (1 - c)) ^ 2 *
          ((∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s) *
              (∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es v s)
            - ∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s * xPair x es v s)
        ≤ 1 - c * (∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s
          + ∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es v s)
          + prob (actProbs c x es) (fun l => HaveWitnesses l u v) := by sorry

end ProphetMatchingEFGT
