-- Prove2me | Theorems.Thm_SemiStreamMWM_lemma_2_1
-- name    : SemiStreamMWM.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:24:15.145945+00:00
-- url     : https://prove2.me/theorems/93d1164f-aa40-4c74-b352-cf57ed67ab10
-- title:
--   Lemma 2.1 — a small potential gap at $t\le\varepsilon/(16\log W)$ gives a fractional $(1-\varepsilon)$-MWM
-- statement:
--   Let $G$ be a graph with integer edge weights $w_e\in[1,W]$, $W\ge8$ a power of two, and let $F_t$, $F_t^*$ be the regularized potential and its minimum over the matching polytope $\mathcal P_G$. Let $0<\varepsilon\le1$ and $0<t\le\varepsilon/(16\log W)$. If $x\in\mathcal P_G$ satisfies
--
--   $$F_t(x)-F_t^*\le\varepsilon\mu_w(G)/2,$$
--
--   then $x$ is a fractional $(1-\varepsilon)$-MWM: $x\in\mathcal P_G$ and $w^\top x\ge(1-\varepsilon)\mu_w(G)$.
--
--   The lemma says that minimizing $F_t$ to additive error $O(\varepsilon)\mu_w(G)$ suffices; it is the endpoint of the phased optimization (Lemma 2.7).
--
--   Differences from the source: none.
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), Lemma 2.1, p.9

import Mathlib
import Definitions.Def_SemiStreamMWM_Graph
import Definitions.Def_SemiStreamMWM_Potential

open Classical

namespace SemiStreamMWM

/-- J. Chen, *Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General
Graphs* (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), Lemma 2.1, p.9.

"Let 0 < ε ≤ 1 and 0 < t ≤ ε/(16 log W). If x ∈ P_G satisfies F_t(x) − F_t^∗ ≤ εµ_w(G)/2, then x
is a fractional (1 − ε)-MWM."

**Formalization Note.** The standing assumptions of the paper (integer weights in `[1, W]`, `W ≥ 8` a
power of two, footnote 1 p.3) are `Standing G w W`. A fractional `(1 − ε)`-MWM (p.8) is a point of
`P_G` with `w^⊤x ≥ (1 − ε)µ_w(G)`; both parts are stated. `log` is base 2. -/
theorem lemma_2_1 {V : Type} [Fintype V] (G : SimpleGraph V) (w : Sym2 V → ℕ) (W : ℕ)
    (ε t : ℝ) (x : G.edgeSet → ℝ) (hst : Standing G w W) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (ht0 : 0 < t) (ht : t ≤ ε / (16 * logW W)) (hx : x ∈ matchingPolytope G)
    (hgap : F G w W t x - Fstar G w W t ≤ ε * mwm G w / 2) :
    x ∈ matchingPolytope G ∧ (1 - ε) * (mwm G w : ℝ) ≤ wdot G (weightVec G w) x := by sorry

end SemiStreamMWM
