-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P53_srm_fidelity_lower_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P53.srm_fidelity_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:31:53.717111+00:00
-- url     : https://prove2.me/theorems/04978cd1-38b4-447c-a54f-a3cbc991ec84
-- title:
--   Fixed-resource SRM fidelity and coding lower bounds
-- statement:
--   Let $N\ge1$ and $d\ge2$ be integers. Alice and Bob have $N$ ordered $d$-dimensional ports, and the input register $C$ has dimension $d$. Write $s=(d-1)/2$ and $|S\rangle=d^{-1/2}\sum_{m=-s}^s(-1)^{s-m}|s,m\rangle|s,-m\rangle$. Put $P_i=|S\rangle\langle S|_{A_iC}\otimes I_{\bar A_i}$, $\sigma_i=d^{-(N-1)}P_i$, and $\rho=\sum_i\sigma_i$. A resource filter $O$ gives $|\Psi_O\rangle=(O_A\otimes I_B)|S\rangle^{\otimes N}$ and obeys $\operatorname{tr}(O^\dagger O)=d^N$. Alice measures $AC$; Bob selects the reported port and discards the others. Entanglement fidelities are tested against a normalized reference-input singlet, with no correction on the selected port.
--
--   Take $O=I$ and the completed SRM $\Pi_i=\rho^{-1/2}\sigma_i\rho^{-1/2}+(I-\operatorname{supp}\rho)/N$. These effects form a deterministic POVM. Its actual entanglement fidelity and every correct port-coding probability satisfy
--   $$F\ge\frac{N}{N+d^2-1},\qquad q_{k|k}=\frac{d^2F}{N}\ge\frac{d^2}{N+d^2-1}.$$
--   The source independently rederives this fixed-resource measurement bound in Appendix C. It is not an inequality for arbitrary measurements. At $N=1$, $F=d^{-2}$ and $q_{k|k}=1$.
-- source:
--   Some remarks on port-based teleportation, arXiv:1506.01555v2, PDF p. 5, VII Eqs.(29)-(30), Appendix C: rederived SRM fidelity and coding probability lower bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P53

open scoped Classical ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

-- Accepted generic matrix and positive-operator interfaces. The support is the
-- orthogonal range projection; all uses below are on positive physical rho.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

/-- PDF p.5, Eqs.(29)-(30), p.7: fixed maximally entangled resource, completed
SRM, and every port's physical coding probability. -/
theorem srm_fidelity_lower_bound (d N : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N) :
    DeterministicPOVM (completedSRM d N) ∧
    pbtFidelity (1 : Op (Ports d N)) (completedSRM d N) ≥
      (N : ℝ) / ((N : ℝ) + (d : ℝ) ^ 2 - 1) ∧
    ∀ k : Fin N,
      codingProbability (1 : Op (Ports d N)) (completedSRM d N k) k =
        (d : ℝ) ^ 2 * pbtFidelity (1 : Op (Ports d N)) (completedSRM d N) / N ∧
      codingProbability (1 : Op (Ports d N)) (completedSRM d N k) k ≥
        (d : ℝ) ^ 2 / ((N : ℝ) + (d : ℝ) ^ 2 - 1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P53

end
