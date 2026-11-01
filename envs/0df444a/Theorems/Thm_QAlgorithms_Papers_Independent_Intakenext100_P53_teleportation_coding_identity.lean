-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P53_teleportation_coding_identity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P53.teleportation_coding_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:29:55.781233+00:00
-- url     : https://prove2.me/theorems/dd0f7d17-9018-481b-bcad-00d668f6099c
-- title:
--   Probabilistic teleportation and port-coding probability identity
-- statement:
--   Let $N\ge1$ and $d\ge2$ be integers. Alice and Bob have $N$ ordered $d$-dimensional ports, and the input register $C$ has dimension $d$. Write $s=(d-1)/2$ and $|S\rangle=d^{-1/2}\sum_{m=-s}^s(-1)^{s-m}|s,m\rangle|s,-m\rangle$. Put $P_i=|S\rangle\langle S|_{A_iC}\otimes I_{\bar A_i}$, $\sigma_i=d^{-(N-1)}P_i$, and $\rho=\sum_i\sigma_i$. A resource filter $O$ gives $|\Psi_O\rangle=(O_A\otimes I_B)|S\rangle^{\otimes N}$ and obeys $\operatorname{tr}(O^\dagger O)=d^N$. Alice measures $AC$; Bob selects the reported port and discards the others. Entanglement fidelities are tested against a normalized reference-input singlet, with no correction on the selected port.
--
--   Use any exact probabilistic protocol with failure outcome $0$. Let $p_i$ be its reference-singlet branch probability. In the coding experiment Bob sends $B_k$ to Alice, identifying it as $C$, and Alice uses exactly the same resource and POVM; denote its actual outcome probabilities by $q_{i|k}$. Then for every successful label $i$,
--   $$q_{i|k}=\begin{cases}d^2p_i,&i=k,\\p_i,&i\ne k,\end{cases}\qquad \sum_k\sum_{i=1}^Nq_{i|k}=(N+d^2-1)\sum_i p_i.$$
--   No equiprobability or permutation assumption is made. Exactness is expressed by the unnormalized branch equation, so a branch with $p_i=0$ is included. This is the operational interface used for the success upper bound.
-- source:
--   Some remarks on port-based teleportation, arXiv:1506.01555v2, PDF p. 4, V Eqs.(20)-(22): probabilistic teleportation/coding probability identity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P53

open scoped Classical ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

-- Accepted generic matrix and positive-operator interfaces. The support is the
-- orthogonal range projection; all uses below are on positive physical rho.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

/-- PDF p.4, Eqs.(20)-(22): probabilities in the same resource and measurement,
including zero-probability successful branches. -/
theorem teleportation_coding_identity (d N : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N)
    (O : Op (Ports d N)) (E : Option (Fin N) → Op (AC d N))
    (hexact : ExactProbabilistic O E) :
    (∀ i k, codingProbability O (E (some i)) k =
      if i = k then (d : ℝ) ^ 2 * pbtBranchProbability O (E (some i))
      else pbtBranchProbability O (E (some i))) ∧
    (∑ k : Fin N, ∑ i : Fin N, codingProbability O (E (some i)) k) =
      ((N : ℝ) + (d : ℝ) ^ 2 - 1) * pbtSuccessProbability O E := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P53

end
