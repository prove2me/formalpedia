-- Prove2me | Theorems.Thm_SantaClausNSW_MaxMin_lemma_3_2
-- name    : SantaClausNSW.MaxMin.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:37:10.399345+00:00
-- url     : https://prove2.me/theorems/166dbdea-5213-48d5-b012-b3dd779e9f16
-- title:
--   Lemma 3.2 — GKPS rounding: right-vertex marginals equal fractional degrees, and matched right vertices are negatively correlated
-- statement:
--   In the setting of §3.1, run GKPS dependent rounding on the bipartite graph of §3.2, with any valid rule choosing cycles and maximal paths. For a right vertex $v$ let $\chi_v\in\{0,1\}$ indicate that $v$ is matched at the end, and let $d_v$ be its fractional degree in the initial graph. Then $\Pr[\chi_v=1]=d_v$ for every right vertex $v$; for every set $Q$ of right vertices
--   $$\mathbb E\Big[\prod_{v\in Q}\chi_v\Big]\le\prod_{v\in Q}d_v;$$
--   and for every set $Q$ of right vertices and every right vertex $u\notin Q$ with $d_u>0$,
--   $$\mathbb E\Big[\prod_{v\in Q}\chi_v\,\Big|\,\chi_u=1\Big]\le\prod_{v\in Q}d_v .$$
--   These are the marginal and negative-correlation properties the failure analysis of Lemma 3.3 rests on.
--
--   Differences from the source:
--   - reading: the bipartite dependent rounding of [GKPS06] (choice of cycle or maximal path left open) → GKPS with any deterministic rule returning a cycle or a maximal (leaf-to-leaf) path of the fractional edges; the statement holds for every such rule; reason: the paper does not fix the choice, so the lemma is stated for all of them
--   - encoding: right vertices: items j with b_j > 0 and u_{i,S} for S ∈ S_i → all items and all pairs (k, S); the extra ones are isolated (degree 0); reason: an isolated vertex is never matched and has d_v = 0, so the claims about it are trivial and the claims about the paper's vertices are unchanged
--   - encoding: E[∏_{v∈Q} χ_v] and E[· | χ_u = 1] → Pr[every v ∈ Q matched] and Pr[all of Q matched ∧ u matched] / Pr[u matched]; reason: the expectation of a product of indicators is the probability of their conjunction; same values
--   - reading: one sentence quantifying "every set Q and every u ∉ Q with d_u > 0" before both inequalities of (8) → the unconditional inequality for every set Q, the conditional one for every Q and u ∉ Q with d_u > 0; reason: the unconditional bound does not involve u, and the proof (p. 13) applies it to Q ∪ {u}, a set that need not miss any vertex of positive degree; the narrower scope is the weaker reading
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 12, Lemma 3.2

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Rounding

namespace SantaClausNSW.MaxMin

/-- **Lemma 3.2** (p. 12). In the setting of §3.1, run GKPS dependent rounding on the bipartite
graph of §3.2 with any valid rule choosing the cycles and maximal paths. For every right vertex
`v`, `Pr[χ_v = 1] = d_v`; for every set `Q` of right vertices, `E[∏_{v ∈ Q} χ_v] ≤ ∏_{v ∈ Q} d_v`;
and for every such `Q` and every right vertex `u ∉ Q` with `d_u > 0`,
`E[∏_{v ∈ Q} χ_v | χ_u = 1] ≤ ∏_{v ∈ Q} d_v`. -/
theorem lemma_3_2 {n m : ℕ} (hn : 0 < n) (st : Setting n m) (hst : st.Valid)
    (rule : GKPSRule n m) (hrule : rule.Valid) :
    (∀ v : RV n m, probOf (gkpsLaw st rule) (fun x => Matched x v) = degree st.x0 v) ∧
    (∀ Q : Finset (RV n m),
      probOf (gkpsLaw st rule) (fun x => ∀ v ∈ Q, Matched x v) ≤ ∏ v ∈ Q, degree st.x0 v) ∧
    ∀ (Q : Finset (RV n m)) (u : RV n m), u ∉ Q → 0 < degree st.x0 u →
      condProbOf (gkpsLaw st rule) (fun x => ∀ v ∈ Q, Matched x v) (fun x => Matched x u) ≤
        ∏ v ∈ Q, degree st.x0 v := by sorry

end SantaClausNSW.MaxMin
