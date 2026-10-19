-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P50_j2_hilbertSchmidt_isomorphism
-- name    : QAlgorithms.Papers.Independent.Dependency50.P50.j2_hilbertSchmidt_isomorphism
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:26:05.353169+00:00
-- url     : https://prove2.me/theorems/acf80d47-15d1-4427-908d-ecb7e5242ebb
-- title:
--   The unnormalized J2 is a Hilbert–Schmidt linear isomorphism
-- statement:
--   Let $n,m>0$ and let $\mathcal L$ be the complex vector space of complex-linear maps $M_n(\mathbb C)\to M_m(\mathbb C)$. Let $E_{ij}$ denote the canonical matrix units and define
--
--   $$J_2(T)=\sum_{i,j=1}^n E_{ij}\otimes T(E_{ij}),\qquad J_1(T)=\sum_{i,j=1}^n E_{ij}^*\otimes T(E_{ij}).$$
--
--   The first tensor factor is the input reference and the second is the output. Write $\langle A,B\rangle_{\rm HS}=\operatorname{Tr}(B^*A)$ and $\langle T,S\rangle_{\mathcal L}=\sum_{ij}\langle T(E_{ij}),S(E_{ij})\rangle_{\rm HS}$. The specified map $J_2$ is a complex-linear bijection onto all operators on $\mathbb C^n\otimes\mathbb C^m$, and for every $T,S\in\mathcal L$,
--
--   $$\langle J_1(T),J_1(S)\rangle_{\rm HS}=\langle J_2(T),J_2(S)\rangle_{\rm HS}=\langle T,S\rangle_{\mathcal L}.$$
--
--   This fixes the actual Hilbert–Schmidt isomorphism, including its unnormalized scale and tensor ordering.
-- source:
--   The Jamio{\l}kowski isomorphism and a conceptionally simple proof for the correspondence between vectors having Schmidt number $k$ and $k$-positive maps, arXiv:quant-ph/0702255v1, PDF p. 5, §IV, equations (4)–(7)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P50

/-- PDF p.5, §IV, equations (4)–(7): J2 is a linear bijection and preserves
the Hilbert–Schmidt pairing, with the same image pairing as J1. -/
theorem j2_hilbertSchmidt_isomorphism {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    Function.Bijective (j2 (n := n) (m := m)) ∧
      ∀ T S : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ),
        hsPair (j2 T) (j2 S) = mapPair T S ∧
          hsPair (j1 T) (j1 S) = hsPair (j2 T) (j2 S) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P50

end
