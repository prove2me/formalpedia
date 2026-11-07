-- Prove2me | Theorems.Thm_RGMISFast_lemma_A_2
-- name    : RGMISFast.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:27:44.157775+00:00
-- url     : https://prove2.me/theorems/222332de-4b93-4012-9bd1-8473f738624e
-- title:
--   Lemma A.2: at most $(4\Delta)^j$ root-connected sets with $j$ non-root vertices
-- statement:
--   Let $G$ be a finite simple graph with all degrees at most $\Delta$ and root $u^*$. For every $j\ge0$, the number of root-connected sets with exactly $j$ vertices other than $u^*$ is at most
--   $$
--   (4\Delta)^j .
--   $$
--
--   This standard count drives the union bound of Lemma A.1.
--
--   **Formalization Note** The sets are counted as vertex sets $A\ni u^*$ with $|A|=j+1$ and $G[A]$ connected.
--
--   Differences from the source: none.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), Lemma A.2, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_RGMISFast_IsRootConnected

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RGMISFast

/-- Lemma A.2 (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), p.29): for every `j ≥ 0`, there are at most `(4∆)^j` root-connected sets with
exactly `j` vertices other than `u∗`.

**Formalization Note** `∆` is any bound on all degrees; no lower bound on `∆` is needed. The
sets are finsets `A` with `|A| = j + 1`, counted by `Set.ncard` (the family is finite). -/
theorem lemma_A_2 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (u : V) (j : ℕ) :
    {A : Finset V | IsRootConnected G u A ∧ A.card = j + 1}.ncard ≤ (4 * Δ) ^ j := by sorry

end RGMISFast
