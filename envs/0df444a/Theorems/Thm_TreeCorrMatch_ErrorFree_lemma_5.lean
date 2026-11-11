-- Prove2me | Theorems.Thm_TreeCorrMatch_ErrorFree_lemma_5
-- name    : TreeCorrMatch.ErrorFree.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:27:39.529199+00:00
-- url     : https://prove2.me/theorems/6ba3dde6-3c09-4d08-907b-4243c25da1a6
-- title:
--   Lemma 5 — on $A_1\cap A_2$ no wrong pair passes the 5-dangling-tree test
-- statement:
--   Fix $n$, an outcome $(G,\tilde G,\pi)$, the algorithm's seeds and parameters, and consider TBAlign without degree cutoff ($\tau=\infty$). If the events $A_1$ and $A_2$ hold, then TBAlign does not match any wrong pair:
--
--   $$M^\infty_{TB}(u,\tilde v)=0\quad\text{for all pairs }(u,\tilde v)\text{ with }\tilde v\ne\tilde u=\pi(u),$$
--
--   whatever order GreedyMatching uses to examine the edges of $W^\infty(u,\tilde v)$.
--
--   This deterministic statement is where the 5-dangling-tree test pays off: five disjoint passing neighbour pairs of a wrong pair would produce a small subgraph of the union graph with two cycles, which $A_2$ excludes.
--
--   Differences from the source:
--   - reading: M^∞_TB(u, ṽ) = GreedyMatching(W^∞(u, ṽ), θ*, 5) with an arbitrary edge order → = 0 for every admissible edge order; reason: the order is arbitrary in the algorithm; the proof holds for every order
--   - encoding: the parameters of TBAlign → arbitrary λ, s, approximator, class map r and seeds; d, θ* from (1); reason: the lemma is deterministic and uses no property of them
--   - encoding: node set [n] → Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 16, Lemma 5 (PDF p. 18)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_AnalysisEvents

namespace TreeCorrMatch.ErrorFree

theorem lemma_5 {Ω₀ : Type} (App : PermApprox Ω₀) (r : OTree → OTree) (lam s : ℝ) (n : ℕ)
    (x : CEROutcome n) (ω : TBIdx n → Ω₀) (hA1 : EventA1 App r lam s x ω) (hA2 : EventA2 x) :
    ∀ u v : Fin n, v ≠ x.2.2 u → ∀ order : List (Fin n × Fin n),
      IsWitnessOrder x.1 x.2.1 u v order → mTB App r lam s ⊤ x.1 x.2.1 ω u v order = false := by sorry

end TreeCorrMatch.ErrorFree
