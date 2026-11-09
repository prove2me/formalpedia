-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_prop_20
-- name    : TFIMPhaseDiagram.Classical.prop_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:03:54.309209+00:00
-- url     : https://prove2.me/theorems/672c5662-a8f9-4f94-b181-847390f08c5e
-- title:
--   Proposition 20 — Open-path covariance product bound
-- statement:
--   Let $\mu$ be the open-chain Ising law with $M\ge1$ spins, arbitrary real edge couplings $K_1,\ldots,K_{M-1}$, and arbitrary real external fields. For $1\le i\le j\le M$,
--   $$|\operatorname{Cov}(\mu)_{i,j}|\le\left|\prod_{k=i}^{j-1}\tanh K_k\right|.$$
--   The empty product for $i=j$ is $1$. This gives the path bound used on the two arcs of a signed cycle.
--
--   Differences from the source:
--   - encoding: indices 1 through M with edges 1 through M-1 → zero-based Fin M and Fin (M-1); reason: The product endpoints shift together; i=j has the empty product 1.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, printed p.12 = PDF p.12, Proposition 20

import Definitions.Def_TFIMPhaseDiagram_Classical_traceSetup

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
/-- Proposition 20, p.12, Eq.(13): signed open-path couplings. -/
theorem prop_20 (M : ℕ) (hM : 1 ≤ M) (K : Fin (M-1) → ℝ) (w : Fin M → ℝ)
    (i j : Fin M) (hij : i ≤ j) :
  |spinCov (openProb K w) i j| ≤
    |∏ k ∈ Finset.univ.filter (fun k : Fin (M-1) => i.val ≤ k.val ∧ k.val < j.val), Real.tanh (K k)| := by sorry
end TFIMPhaseDiagram.Classical
