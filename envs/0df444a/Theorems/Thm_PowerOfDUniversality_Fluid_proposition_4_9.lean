-- Prove2me | Theorems.Thm_PowerOfDUniversality_Fluid_proposition_4_9
-- name    : PowerOfDUniversality.Fluid.proposition_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:40:35.046162+00:00
-- url     : https://prove2.me/theorems/bb07267e-6910-40ee-b654-ea15f3ef7651
-- title:
--   Proposition 4.9 — if d(N) → ∞, JSQ(d(N)) has the same fluid limit as JSQ
-- statement:
--   Fix a buffer $b\ge1$ and a normalized arrival rate $\lambda\in[0,1)$. Suppose the ordinary JSQ policy has the fluid limit (4.5): for every sequence of server counts $N_j\to\infty$ with arrival rates $\lambda_j/N_j\to\lambda$ and deterministic initial states with $\mathbf q^{N_j}(0)\to\mathbf q^\infty\in\mathcal S$ in $\ell_1$, any subsequence of the fluid-scaled JSQ processes has a further subsequence converging weakly (Skorohod $J_1$, $\ell_1$) to a solution of (2.1). Then the JSQ($d(N)$) scheme with $d(N)\to\infty$ has the same fluid limit: for systems with $N=1,2,\dots$ servers, $\lambda(N)/N\to\lambda$, $1\le d(N)\le N$, $d(N)\to\infty$ and deterministic initial states with $\mathbf q^{d(N)}(0)\to\mathbf q^\infty$ in $\ell_1$, any subsequence of $\{\mathbf q^{d(N)}(t)\}_{t\ge0}$ has a further subsequence converging weakly to a solution of (2.1).
--
--   In words: if $d(N)\to\infty$ as $N\to\infty$, then the JSQ($d(N)$) scheme and the ordinary JSQ policy have the same fluid limit.
--
--   **Formalization Note** "Have the same fluid limit" is rendered as the paper's own reduction ("Having proved Theorem 4.1, it suffices to prove the universality property stated in the next proposition. This will complete the proof of Theorem 2.1."): the JSQ fluid limit for all server-count sequences implies the conclusion of Theorem 2.1. The hypothesis ranges over all sequences because the proof applies it to $\bar N=N-n(N)$ servers.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, pp. 27–28, Proposition 4.9 and its proof

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace
import Definitions.Def_PowerOfDUniversality_Fluid_Universality

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid

/-- **Proposition 4.9** (p. 27): if `d(N) → ∞`, the JSQ(d(N)) scheme and the ordinary JSQ policy
have the same fluid limit. Rendered as the paper's reduction of Theorem 2.1 to Theorem 4.1: for a
buffer `b ≥ 1` and `λ ∈ [0, 1)`, if the JSQ fluid limit (4.5) holds for every sequence of server
counts `N_j → ∞` with `λ_j / N_j → λ`, then the JSQ(d(N)) fluid limit (2.1) of Theorem 2.1
holds whenever `d(N) → ∞`. -/
theorem proposition_4_9 (b : ℕ∞) (hb : 1 ≤ b) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) :
    JSQFluidLimit b lam → JSQdFluidLimit b lam := by sorry

end PowerOfDUniversality.Fluid
