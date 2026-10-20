-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_propositionC29
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.propositionC29
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:35:50.196562+00:00
-- url     : https://prove2.me/theorems/aaac6cde-5a56-4203-9368-22cb8ee16511
-- title:
--   Trade-off between a channel and its complementary channel
-- statement:
--   Let $d,p\ge1$ and let $K_1,\ldots,K_p\in M_d(\mathbb C)$ be a normalized Kraus family, defining $\Phi(X)=\sum_iK_iXK_i^*$. Its Stinespring complementary channel is $\Phi^C:M_d(\mathbb C)\to M_p(\mathbb C)$ with entries $\Phi^C(X)_{ij}=\operatorname{Tr}(K_j^*K_iX)$. For the one-shot zero-error classical and quantum capacities in bits,
--
--   $$2^{C_0(\Phi^C)}+2^{Q_0(\Phi)}\le d+1.$$
--
--   This bounds the joint perfectly distinguishable classical messages at the environment and recoverable quantum dimensions at the output.
--
--   **Formalization Note** The printed complementary-channel entries interchange $i,j$. The genuine CP complement above corrects that transpose. The displayed trade-off has capacities in exponents, as confirmed visually on p.32.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 32, Proposition C.29

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P37

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)

open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)

open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

/-- Proposition C.29, PDF pp.32–33: powers of two, not twice the capacities.
The genuine CP Stinespring complement uses the index correction documented
in krausDilation. Any normalized Kraus representation is permitted. -/
theorem propositionC29 {d p : ℕ} (hd : 0 < d) (hp : 0 < p)
    (K : Fin p → Operator d) (hK : IsKrausFamily K) :
    (2 : ℝ) ^ classicalCapacity (complementaryChannel (krausDilation K)) +
      (2 : ℝ) ^ quantumCapacity (krausApply K) ≤ (d : ℝ) + 1 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
