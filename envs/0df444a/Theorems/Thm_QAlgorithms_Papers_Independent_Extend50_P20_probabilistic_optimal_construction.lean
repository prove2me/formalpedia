-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P20_probabilistic_optimal_construction
-- name    : QAlgorithms.Papers.Independent.Extend50.P20.probabilistic_optimal_construction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:06:45.043014+00:00
-- url     : https://prove2.me/theorems/0dbafe41-f05d-4739-81ab-8d49d399972b
-- title:
--   Optimal probabilistic effects and normalized resource
-- statement:
--   Let $d\ge1$ and $1\le k\le N$. For each Young diagram $\lambda$ of height at most $d$, let $m_\lambda$ be its actual Schur–Weyl multiplicity, $d_\lambda$ its Specht dimension, and $P_\lambda$ its full physical isotypic projector. Put $S_N=\sum_{\nu\vdash N,\,h(\nu)\le d}m_\nu^2$ and $L=k!\binom Nk$. For an ordered injective port tuple $i$, let $P_i^+$ pair the selected ports with the $k$ input positions by normalized Bell projectors, and let $P_\alpha^{(i)}$ act on the unselected ports. Set
--
--   $$\Pi_i=P_i^+\otimes\sum_{\alpha\vdash N-k,\,h(\alpha)\le d}\frac{d^{N+k}m_\alpha}{L\,d_\alpha S_N}P_\alpha^{(i)},\qquad O_A=\sqrt{d^N}\sum_{\mu\vdash N,\,h(\mu)\le d}\sqrt{\frac{m_\mu}{d_\mu S_N}}P_\mu.$$
--
--   These operators satisfy $\operatorname{Tr}(O_A^\dagger O_A)=d^N$ and attain the optimal probabilistic MPBT success for all inputs. There are positive physical conclusive effects and a positive failure effect summing to identity, whose conclusive effects rotate by congruence with $O_A\otimes I$ to the displayed $\Pi_i$.
--
--   This constructs the resource and measurements realizing the optimum.
-- source:
--   Optimal Multi-port-based Teleportation Schemes, arXiv:2011.09256v3, PDF p. 11, Theorem 5 / Eq. (36)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P20

noncomputable section

open scoped BigOperators Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Extend50.P20

attribute [local instance] Classical.propDecidable

/-- Theorem 5, PDF p.11, Eq.(36), verified against pp.16,18, Eqs.(52),(53),(69).
S_N divides u_alpha and occurs under the square root in O_A. Resource
normalization and physical POVM completion are conclusions, not assumptions. -/
theorem probabilistic_optimal_construction (d N k : ℕ)
    (hd : 0 < d) (hk : 1 ≤ k) (hkN : k ≤ N) :
    let O := optimalProbOperation d N
    let T := optimalProbTheta d N k
    RealizesMpbtEffects O (fun i => successEffect i (T i)) ∧
      ProbFeasible (Matrix.conjTranspose O * O) T ∧
      IsGreatest (probValues d N k) (probScore T) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P20

end
