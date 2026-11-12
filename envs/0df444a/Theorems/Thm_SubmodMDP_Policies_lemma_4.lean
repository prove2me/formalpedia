-- Prove2me | Theorems.Thm_SubmodMDP_Policies_lemma_4
-- name    : SubmodMDP.Policies.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:22.707344+00:00
-- url     : https://prove2.me/theorems/2bc0cca2-130e-435d-bf7a-21b7011e87e3
-- title:
--   Lemma 4 — $\mathrm{RRR}$ is well defined, returns layer-spanning paths and preserves vertex marginals
-- statement:
--   Let $G$ be a layered graph with $V=V_1\cup\dots\cup V_H$, $H=d^r$ with $d\in\mathbb Z_{\ge2}$ and $r\in\mathbb Z_{\ge0}$, and let $x\in Q^{(r)}$. Then recursive randomized rounding (Algorithm 1) applied to $x$
--
--   1. is well defined: with probability one it never samples from weights that are not a probability distribution and never conditions on a vertex $u$ with $x_u=0$;
--   2. returns a layer-spanning path; and
--   3. its output path $P$ satisfies
--   $$\mathbb P[v\in P]=x_v\qquad\text{for all }v\in V.$$
--
--   Marginal preservation is what later turns linear constraints on $x$ into constraints on the expected behaviour of the rounded path.
--
--   Differences from the source:
--   - encoding: x ∈ ℝ^{(V choose ≤ r+1)} → a function on all vertex sets of which only the coordinates with |I| ≤ r+1 are read; reason: coordinates outside the index set are never used by Q^(r), RRR or the linear functions; same instances
--   - reading: (i) recursive randomized rounding is well defined → the outcome none of the partial formalization of Algorithm 1 has probability 0; none is returned exactly when the weights of line 2 are not a probability vector or the algorithm conditions on a vertex u with x_u = 0; reason: these are the only steps of Algorithm 1 that can be undefined, and they are the ones the paper's proof checks
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), Lemma 4, p. 7 (PDF p. 8); Algorithm 1, p. 6 (PDF p. 7)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_Layered

namespace SubmodMDP.Policies

/-- Lemma 4 (PDF p. 8): for a layered graph with `H = d^r` (`d ≥ 2`) and `x ∈ Q^(r)`, recursive
randomized rounding (i) is well defined (it never fails), (ii) returns a layer-spanning path, and
(iii) `P[v ∈ P] = x_v` for every vertex `v`. -/
theorem lemma_4 (G : LGraph) (hG : G.WF) (d r : ℕ) (hd : 2 ≤ d) (hH : G.H = d ^ r)
    (x : Finset (Fin G.N) → ℝ) (hx : InQ G r x) :
    none ∉ (RRR G d r x).support ∧
    (∀ P : List (Fin G.N), some P ∈ (RRR G d r x).support → IsLSPath G P) ∧
    ∀ v : Fin G.N,
      (RRR G d r x).toOuterMeasure {o | ∃ P, o = some P ∧ v ∈ P} = ENNReal.ofReal (x {v}) := by sorry

end SubmodMDP.Policies
