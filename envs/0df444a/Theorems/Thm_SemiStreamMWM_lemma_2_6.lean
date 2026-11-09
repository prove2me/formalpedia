-- Prove2me | Theorems.Thm_SemiStreamMWM_lemma_2_6
-- name    : SemiStreamMWM.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:25:25.845344+00:00
-- url     : https://prove2.me/theorems/24cdc5db-9326-4682-a8cb-dfe0420afec3
-- title:
--   Lemma 2.6 — halving $t$ keeps feasibility and the initial-gap condition
-- statement:
--   Let $G$ have integer weights in $[1,W]$, $W\ge8$ a power of two; let $c\ge1$ be the oracle constant and $0<t\le1/(32\log W)$, $\delta=t\log W$. Let $x\in\mathcal P_{G,\delta}$ satisfy $F_t(x)-F_t^*\le2c^2\delta\mu_w(G)$, and set $t'=t/2$ and $\delta'=t'\log W=\delta/2$. Then
--
--   $$x\in\mathcal P_{G,\delta'}\quad\text{and}\quad F_{t'}(x)-F_{t'}^*\le32c^2\delta'\mu_w(G).$$
--
--   The output of one phase therefore satisfies the starting condition of Lemma 2.5 in the next phase.
--
--   Differences from the source:
--   - encoding: the standing assumptions stated once for the paper and for §2.1 (integer weights in [1, W], W ≥ 8 a power of two, 0 < t ≤ 1/(32 log W)) → hypotheses `Standing G w W`, `0 < t`, `t ≤ 1/(32 * logW W)`; reason: trap 19: the section's assumptions are binders; no instance changes
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), Lemma 2.6, p.12

import Mathlib
import Definitions.Def_SemiStreamMWM_Graph
import Definitions.Def_SemiStreamMWM_Potential

open Classical

namespace SemiStreamMWM

/-- J. Chen (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), Lemma 2.6, p.12.

"Let x ∈ P_{G,δ} satisfy F_t(x) − F_t^∗ ≤ 2c²δµ_w(G), and set t′ = t/2 and δ′ = t′ log W = δ/2. Then
x ∈ P_{G,δ′} and F_{t′}(x) − F_{t′}^∗ ≤ 32c²δ′µ_w(G)."

**Formalization Note.** `c ≥ 1` is the oracle constant of Definition 2.4 (p.11); §2.1's
`0 < t ≤ 1/(32 log W)` and footnote 1 (`Standing`) are hypotheses. `δ′ = t′ log W` is
`delta W (t / 2)`, which equals `δ/2` by definition. -/
theorem lemma_2_6 {V : Type} [Fintype V] (G : SimpleGraph V) (w : Sym2 V → ℕ) (W : ℕ) (c t : ℝ)
    (x : G.edgeSet → ℝ) (hc : 1 ≤ c) (hst : Standing G w W) (ht0 : 0 < t)
    (ht : t ≤ 1 / (32 * logW W)) (hx : x ∈ truncPolytope G (delta W t))
    (hgap : F G w W t x - Fstar G w W t ≤ 2 * c ^ 2 * delta W t * mwm G w) :
    x ∈ truncPolytope G (delta W (t / 2)) ∧
      F G w W (t / 2) x - Fstar G w W (t / 2) ≤ 32 * c ^ 2 * delta W (t / 2) * mwm G w := by sorry

end SemiStreamMWM
