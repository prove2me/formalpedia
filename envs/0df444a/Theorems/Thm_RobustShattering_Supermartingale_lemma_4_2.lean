-- Prove2me | Theorems.Thm_RobustShattering_Supermartingale_lemma_4_2
-- name    : RobustShattering.Supermartingale.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:43:40.887207+00:00
-- url     : https://prove2.me/theorems/e59963b5-b765-4b43-b7c9-809b6fe7c319
-- title:
--   Lemma 4.2 — at most e^t·n·Δ^{x(t−1)} x-connected sets of size t (Δ^x replaceable by max_v |B^x(v)∖{v}|)
-- statement:
--   Let $\Delta\ge2$, $t\ge1$ and $x\ge0$ be integers, and let $G$ be a graph on $n$ vertices in which every vertex has degree at most $\Delta$. Then the number $N_{x,t}$ of $x$-connected vertex sets of size $t$ (sets inducing a connected subgraph of the power graph $G^x$) satisfies
--   $$N_{x,t}\le e^t\cdot n\,\Delta^{x(t-1)}\qquad\text{and}\qquad N_{x,t}\le e^t\cdot n\,M^{t-1},\quad M=\max_{v\in V}\big|B^x(v)\setminus\{v\}\big|,$$
--   where $B^x(v)$ is the set of vertices at distance at most $x$ from $v$ in $G$.
--
--   The count is the union-bound budget of the Shattering Lemma (Lemma 4.3): its base-$e$ factor, rather than the $4^t$ of earlier proofs, is what makes the shattering lemma work down to $\Delta=3$.
--
--   **Formalization Note.** $N_{x,t}$ is `Set.ncard` of the finsets $S$ with $|S|=t$ and `XConnected G x S`, compared as a real number. $M$ is the supremum over all vertices of `Set.ncard (ball G v x \ {v})` (it is $0$ when $V$ is empty, where both sides are $0$). Since $t\ge1$, the natural-number exponents $x(t-1)$ and $t-1$ have no truncation.
--
--   Differences from the source:
--   - generalization: graph with maximum degree $\Delta$ → every vertex degree at most $\Delta$; reason: a graph of maximum degree $\Delta$ satisfies the hypothesis, and the proof only uses the upper bound $|B^x(v)\setminus\{v\}|\le\Delta^x$
--   - encoding: "number of $x$-connected sets of size $t$" → `Set.ncard` of the finsets of cardinality $t$ that are `XConnected`, as a real number; reason: $V$ is finite, so this is the count
--   - encoding: $\max_{v\in V}|B^x(v)\setminus\{v\}|$ → `Finset.univ.sup` of `Set.ncard (ball G v x \ {v})`; reason: the maximum over a finite nonempty vertex set; for $n=0$ both sides of the bound are $0$
-- source:
--   Davies-Peck, Ghaffari, Halldórsson, Maus, Nolin, Robust Shattering Arguments, arXiv:2606.27847 (held manuscript, sha256 21726e7f…8128), p. 12, Lemma 4.2

import Mathlib
import Definitions.Def_LocalLLL_Main_GraphModel
import Definitions.Def_RobustShattering_Supermartingale_XConnected

namespace RobustShattering.Supermartingale

/-- Lemma 4.2 (p. 12): let `G` be a graph on `n` vertices with every degree at most `Δ`, where
`Δ ≥ 2`, `t ≥ 1` and `x ≥ 0` are integers. The number of `x`-connected vertex sets of size `t` is
at most `e^t · n · Δ^{x(t-1)}`, and also at most `e^t · n · M^{t-1}` with
`M = max_v |B^x(v) \ {v}|`. -/
theorem lemma_4_2 {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ t x : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (ht : 1 ≤ t) :
    (({S : Finset V | S.card = t ∧ XConnected G x (S : Set V)}.ncard : ℕ) : ℝ)
        ≤ Real.exp t * (Fintype.card V : ℝ) * (Δ : ℝ) ^ (x * (t - 1)) ∧
      (({S : Finset V | S.card = t ∧ XConnected G x (S : Set V)}.ncard : ℕ) : ℝ)
        ≤ Real.exp t * (Fintype.card V : ℝ) *
          ((Finset.univ.sup fun v : V => (LocalLLL.Main.ball G v x \ {v}).ncard : ℕ) : ℝ)
            ^ (t - 1) := by sorry

end RobustShattering.Supermartingale
