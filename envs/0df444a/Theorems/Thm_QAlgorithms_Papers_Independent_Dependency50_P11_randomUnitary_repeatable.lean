-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P11_randomUnitary_repeatable
-- name    : QAlgorithms.Papers.Independent.Dependency50.P11.randomUnitary_repeatable
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:33:38.645812+00:00
-- url     : https://prove2.me/theorems/cd5e4243-652a-4eb9-8c5c-23ed66cb6004
-- title:
--   Random-unitary channels have finite repeatable implementations
-- statement:
--   Let $d\ge1$ and let $\mathcal E$ be a completely positive, trace-preserving linear map on operators on $\mathbb C^d$. Suppose it has a finite decomposition $\mathcal E(X)=\sum_jp_jU_jXU_j^\dagger$, where each $U_j$ is unitary, $0\le p_j\le1$, and $\sum_jp_j=1$. Then there exist a positive finite memory dimension $m$, a normalized memory state $\xi$, and one unitary $U$ on $\mathbb C^m\otimes\mathbb C^d$ such that
--
--   $$\rho^{\rm out}_j=\mathcal E(\rho_j)\qquad(j\ge1)$$
--
--   for every sequence of independent input density matrices. Each use applies this same unitary to the actual current memory and a fresh input, with no reset or extra environment. The claim is equality of individual output marginals, allowing correlations among outputs.
--
--   This gives a finite reusable implementation of every finite random-unitary channel.
-- source:
--   Repeatable quantum memory channels, arXiv:0808.3851v1, PDF p. 3, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P11

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

/-- Theorem 1, PDF p.3 (finite-memory conclusion on p.4): every finite random-unitary
channel has one finite device implementing every individual use on every product history. -/
theorem randomUnitary_repeatable {d : ℕ} (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) (hRU : IsRandomUnitary E) :
    HasFiniteRepeatableImplementation E := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P11

end
