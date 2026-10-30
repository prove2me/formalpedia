-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P20_probabilistic_optimal_success
-- name    : QAlgorithms.Papers.Independent.Extend50.P20.probabilistic_optimal_success
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:05:23.37473+00:00
-- url     : https://prove2.me/theorems/6f7c2c15-cb5f-401a-8d56-766289e66bd7
-- title:
--   Optimal probabilistic MPBT success
-- statement:
--   Let $d\ge1$ be the local dimension and $1\le k\le N$. Optimize jointly over pure resources $(O_A\otimes I)|\phi_d\rangle^{\otimes N}$ and Alice's physical POVM, where $\operatorname{Tr}(O_A^\dagger O_A)=d^N$ and $|\phi_d\rangle=d^{-1/2}\sum_{j=1}^d|j,j\rangle$. Outcomes are ordered injective $k$-tuples of ports; Bob only selects and orders those ports. Successful outcomes transmit every $k$-system input exactly, including inputs entangled with a reference. Then the maximum averaged success probability is attained and equals
--
--   $$p_{\mathrm{opt}}(d,N,k)=\frac{N!\,(d^2+N-k-1)!}{(N-k)!\,(d^2+N-1)!}.$$
--
--   This evaluates the optimal conclusive protocol. **Formalization Note** The attained maximum is stated for the full equivalent SDP (17)–(18) with exact-success factorization (49), without restricting to a symmetric ansatz.
-- source:
--   Optimal Multi-port-based Teleportation Schemes, arXiv:2011.09256v3, PDF p. 10, Theorem 3 / Eq. (33)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P20

noncomputable section

open scoped BigOperators Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Extend50.P20

attribute [local instance] Classical.propDecidable

/-- Theorem 3, PDF p.10, Eq.(33); Appendix A pp.15-18. This is an attained
optimum of the full conclusive SDP, not a symmetry-restricted bound.
The protocol permits k=N, retained here although the telescoping proof in
Appendix D only explicitly treats k<N. -/
theorem probabilistic_optimal_success (d N k : ℕ)
    (hd : 0 < d) (hk : 1 ≤ k) (hkN : k ≤ N) :
    IsGreatest (probValues d N k) (factorialRatio d N k) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P20

end
