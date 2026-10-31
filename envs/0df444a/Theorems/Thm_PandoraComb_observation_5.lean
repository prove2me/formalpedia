-- Prove2me | Theorems.Thm_PandoraComb_observation_5
-- name    : PandoraComb.observation_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:09:38.30355+00:00
-- url     : https://prove2.me/theorems/18001972-ce19-470b-9c1a-7c4fb49ffae8
-- title:
--   Observation 5 — $p(\pi)=p(\pi_A)+p(\pi_B)$ for every partition $\pi=A\uplus B$
-- statement:
--   Let $\pi=(i_1,\dots,i_k)$ be an impulsive strategy (distinct boxes) on a Bernoulli instance with probabilities $p_i$, and let $A,B$ be a partition of the set of boxes of $\pi$. With $p(\pi)=1-\prod_{j=1}^k(1-p_{i_j})$ and $p(\pi_P)=\sum_{j:\,i_j\in P}\prod_{l<j}(1-p_{i_l})\,p_{i_j}$ for the impulsive strategies with dummies,
--
--   $$p(\pi)=p(\pi_A)+p(\pi_B).$$
--
--   The probability that $\pi$ finds a non-zero value splits along the partition; this is used together with Lemma 3.3 in the proof of Lemma 3.1.
--
--   Differences from the source:
--   - generalization: probabilities p_i ∈ [0, 1] (p_i > 0 in §3.1), boxes in [n] → any real numbers p i, boxes in any type ι with decidable equality; reason: the identity is algebraic (a telescoping sum); the paper's probabilities and boxes are an instance
--   - encoding: p(π), p(π_A), p(π_B) as probabilities of the events "some inspected box is non-zero" (pp.10–11) → the closed forms pL p l = 1 − ∏(1 − p_i) and pD p l P; reason: these are the paper's own formulas: Observation 2 (p.10) and the dummies example (p.11)
-- source:
--   Berger, Ezra, Feldman & Fusco, Pandora’s Problem with Combinatorial Cost, arXiv:2303.01078v1, Observation 5, p.12

import Definitions.Def_PandoraComb_ClosedForms

namespace PandoraComb

/-- **Observation 5** (arXiv:2303.01078v1, p.12): "For any impulsive strategy π ⊆ [n] and for any
partition π = A ⊍ B of the set of boxes corresponding to π, we have p(π) = p(π_A) + p(π_B)."

**Formalization Note.** The impulsive strategy is the tuple `l` without repetition; `p(π)` is
`pL p l = 1 − ∏ (1 − p_i)` (p.10) and `p(π_A)`, `p(π_B)` are the probabilities `pD` for the
strategies with dummies (p.11). The probabilities `p i` may be any reals. -/
theorem observation_5 {ι : Type*} [DecidableEq ι] (p : ι → ℝ) (l : List ι) (hl : l.Nodup)
    (A B : Finset ι) (hAB : Disjoint A B) (hcover : A ∪ B = l.toFinset) :
    pL p l = pD p l A + pD p l B := by sorry

end PandoraComb
