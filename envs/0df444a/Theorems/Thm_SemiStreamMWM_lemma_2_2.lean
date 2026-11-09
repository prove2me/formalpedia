-- Prove2me | Theorems.Thm_SemiStreamMWM_lemma_2_2
-- name    : SemiStreamMWM.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:24:05.316199+00:00
-- url     : https://prove2.me/theorems/fac4f4c2-89dc-41b1-8325-5bd9fa432980
-- title:
--   Lemma 2.2 — progress from shrinking, and the curvature bound for bounded directions
-- statement:
--   Let $G$ have integer weights in $[1,W]$, $W\ge8$ a power of two; fix $0<t\le1/(32\log W)$, $\delta=t\log W$, and $\eta$ the largest power of two not exceeding $t\delta/128$. Let $x\in\mathcal P_{G,\delta}$ and write $A$ for the unsigned incidence matrix, $(Ad)_v=\sum_{e\ni v}d_e$.
--
--   1. If $-\nabla F_t(x)^\top x\le-\delta\mu_w(G)/8$, then $$F_t(x-\eta x)\le F_t(x)-\tfrac\eta2\nabla F_t(x)^\top x.$$
--   2. If $-\nabla F_t(x)^\top x\ge-2\delta\mu_w(G)$, then for every $d$ with $\|Ad\|_\infty\le1$ and $\|Ad\|_1\le4\mu(G)$, $$F_t(x+\eta d)\le F_t(x)+\eta\nabla F_t(x)^\top d+2\eta^2\mu_w(G)/t.$$
--
--   The two cases are the progress guarantees used by every iteration of Algorithm 2.1.
--
--   Differences from the source:
--   - encoding: the standing assumptions stated once for the paper and for §2.1 (integer weights in [1, W], W ≥ 8 a power of two, 0 < t ≤ 1/(32 log W)) → hypotheses `Standing G w W`, `0 < t`, `t ≤ 1/(32 * logW W)`; reason: trap 19: the section's assumptions are binders; no instance changes
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), Lemma 2.2, p.10; §2.1 p.10

import Mathlib
import Definitions.Def_SemiStreamMWM_Graph
import Definitions.Def_SemiStreamMWM_Potential

open Classical

namespace SemiStreamMWM

/-- J. Chen (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), Lemma 2.2, p.10, with the
standing phase parameters of §2.1, p.10.

"Let x ∈ P_{G,δ}.
1. If −∇F_t(x)^⊤x ≤ −δµ_w(G)/8, then F_t(x − ηx) ≤ F_t(x) − (η/2)∇F_t(x)^⊤x.
2. If −∇F_t(x)^⊤x ≥ −2δµ_w(G), then F_t(x + ηd) ≤ F_t(x) + η∇F_t(x)^⊤d + 2η²µ_w(G)/t for any d with
‖Ad‖_∞ ≤ 1 and ‖Ad‖_1 ≤ 4µ(G)."

**Formalization Note.** §2.1 fixes `0 < t ≤ 1/(32 log W)`, `δ = t log W` and `η` the largest power
of two `≤ tδ/128`; these are `delta W t`, `eta W t`. `Standing` is footnote 1. `(Ad)_v` is
`deg G d v`, so `‖Ad‖_∞ ≤ 1` is `∀ v, |deg G d v| ≤ 1` and `‖Ad‖_1 = Σ_v |deg G d v|`. The hypothesis
`−∇F_t(x)^⊤x ≤ −δµ_w/8` is written `δµ_w/8 ≤ ∇F_t(x)^⊤x`, and `−∇F_t(x)^⊤x ≥ −2δµ_w` is written
`∇F_t(x)^⊤x ≤ 2δµ_w`. -/
theorem lemma_2_2 {V : Type} [Fintype V] (G : SimpleGraph V) (w : Sym2 V → ℕ) (W : ℕ) (t : ℝ)
    (x : G.edgeSet → ℝ) (hst : Standing G w W) (ht0 : 0 < t) (ht : t ≤ 1 / (32 * logW W))
    (hx : x ∈ truncPolytope G (delta W t)) :
    (delta W t * mwm G w / 8 ≤ wdot G (gradF G w W t x) x →
      F G w W t (x - eta W t • x) ≤ F G w W t x - (eta W t / 2) * wdot G (gradF G w W t x) x) ∧
    (wdot G (gradF G w W t x) x ≤ 2 * delta W t * mwm G w →
      ∀ d : G.edgeSet → ℝ, (∀ v, |deg G d v| ≤ 1) → ∑ v, |deg G d v| ≤ 4 * (mcm G : ℝ) →
        F G w W t (x + eta W t • d) ≤
          F G w W t x + eta W t * wdot G (gradF G w W t x) d + 2 * eta W t ^ 2 * mwm G w / t) := by sorry

end SemiStreamMWM
