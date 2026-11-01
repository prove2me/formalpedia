-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P53_probabilistic_success_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P53.probabilistic_success_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:29:24.293991+00:00
-- url     : https://prove2.me/theorems/1ae801c7-4b69-47ad-a826-64265a2df438
-- title:
--   Universal probabilistic-PBT success bound
-- statement:
--   Let $N\ge1$ and $d\ge2$ be integers. Alice and Bob have $N$ ordered $d$-dimensional ports, and the input register $C$ has dimension $d$. Write $s=(d-1)/2$ and $|S\rangle=d^{-1/2}\sum_{m=-s}^s(-1)^{s-m}|s,m\rangle|s,-m\rangle$. Put $P_i=|S\rangle\langle S|_{A_iC}\otimes I_{\bar A_i}$, $\sigma_i=d^{-(N-1)}P_i$, and $\rho=\sum_i\sigma_i$. A resource filter $O$ gives $|\Psi_O\rangle=(O_A\otimes I_B)|S\rangle^{\otimes N}$ and obeys $\operatorname{tr}(O^\dagger O)=d^N$. Alice measures $AC$; Bob selects the reported port and discards the others. Entanglement fidelities are tested against a normalized reference-input singlet, with no correction on the selected port.
--
--   Let $\{\Pi_0,\Pi_1,\ldots,\Pi_N\}$ be an arbitrary POVM, with $0$ indicating failure, which teleports the input exactly in every successful branch. Let $p_i$ be the probability of branch $i$ in the reference-singlet experiment, and $p=\sum_{i=1}^Np_i$. Then
--   $$p\le\frac{N}{N+d^2-1}.$$
--   In the associated coding experiment Bob sends $B_k$ to Alice and she uses this same measurement. Equality in the bound requires $q_{0|k}=0$ for every $k$, where $q_{0|k}$ is the actual failure probability in that experiment. There is no symmetry or maximally entangled-resource restriction, and no general attainability claim. This is the paper's alternative derivation of the known numerical bound.
-- source:
--   Some remarks on port-based teleportation, arXiv:1506.01555v2, PDF p. 4, V Eqs.(19)-(22): rederived general probabilistic-PBT upper bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P53

open scoped Classical ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

-- Accepted generic matrix and positive-operator interfaces. The support is the
-- orthogonal range projection; all uses below are on positive physical rho.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

/-- PDF p.4, Eqs.(19)-(22): universal bound and necessary coding saturation. -/
theorem probabilistic_success_bound (d N : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N)
    (O : Op (Ports d N)) (E : Option (Fin N) → Op (AC d N))
    (hexact : ExactProbabilistic O E) :
    pbtSuccessProbability O E ≤ (N : ℝ) / ((N : ℝ) + (d : ℝ) ^ 2 - 1) ∧
    (pbtSuccessProbability O E = (N : ℝ) / ((N : ℝ) + (d : ℝ) ^ 2 - 1) →
      ∀ k, codingProbability O (E none) k = 0) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P53

end
