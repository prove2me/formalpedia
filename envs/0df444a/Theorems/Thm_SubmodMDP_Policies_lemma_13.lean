-- Prove2me | Theorems.Thm_SubmodMDP_Policies_lemma_13
-- name    : SubmodMDP.Policies.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:13:10.345194+00:00
-- url     : https://prove2.me/theorems/88c4d76a-bda5-4df0-8c32-fe723227618a
-- title:
--   Lemma 13 — $\mathrm{MDP}(x)=\mathrm{RRR}(x)$
-- statement:
--   Let $G$ be a layered MDP graph with $H=d^r$ ($d\ge2$, $r\ge1$), and let $x\in Q^{(r)}$ satisfy (7). Let $\mathrm{MDP}(x)$ be the distribution over layer-spanning paths obtained from repeatedly applying Algorithm 4 on the previous vertices and $x$. Then
--   $$\mathrm{MDP}(x)=\mathrm{RRR}(x).$$
--
--   This identity transfers the approximation guarantee of Lemma 7, stated for $\mathrm{RRR}(x)$, to the policy of Algorithm 4.
--
--   Differences from the source:
--   - encoding: MDP(x) and RRR(x) as distributions over layer-spanning paths → equality of the two laws on optional vertex lists, where none records a failure (error, invalid weights, or an undefined step of Algorithm 1); reason: the partial formalizations of Algorithms 1 and 4; the equality includes that both fail with the same probability, which is 0 by Lemmas 4 and 12
--   - encoding: x ∈ ℝ^{(V choose ≤ r+1)} → a function on all vertex sets of which only the coordinates with |I| ≤ r+1 are read; reason: coordinates outside the index set are never used by Q^(r), RRR or the linear functions; same instances
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), Lemma 13, p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_GraphMDP

namespace SubmodMDP.Policies

/-- Lemma 13 (PDF p. 19): for `x ∈ Q^(r)` satisfying (7), the law `MDP(x)` of the path obtained
by repeatedly applying Algorithm 4 equals `RRR(x)`. -/
theorem lemma_13 (M : GMDP) (hM : M.WF) (d r : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r)
    (hH : M.G.H = d ^ r) (x : Finset (Fin M.G.N) → ℝ) (hx : InQ M.G r x) (h7 : Sat7 M r x) :
    MDPlaw M d x = RRR M.G d r x := by sorry

end SubmodMDP.Policies
