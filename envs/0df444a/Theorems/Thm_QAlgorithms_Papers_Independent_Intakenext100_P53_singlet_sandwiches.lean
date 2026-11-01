-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P53_singlet_sandwiches
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P53.singlet_sandwiches
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:35:05.148002+00:00
-- url     : https://prove2.me/theorems/849a73b7-80b5-4db9-a731-0dea75ce064c
-- title:
--   Exact singlet sandwiches of rho and its support
-- statement:
--   Let $N\ge1$ and $d\ge2$ be integers. Alice and Bob have $N$ ordered $d$-dimensional ports, and the input register $C$ has dimension $d$. Write $s=(d-1)/2$ and $|S\rangle=d^{-1/2}\sum_{m=-s}^s(-1)^{s-m}|s,m\rangle|s,-m\rangle$. Put $P_i=|S\rangle\langle S|_{A_iC}\otimes I_{\bar A_i}$, $\sigma_i=d^{-(N-1)}P_i$, and $\rho=\sum_i\sigma_i$. A resource filter $O$ gives $|\Psi_O\rangle=(O_A\otimes I_B)|S\rangle^{\otimes N}$ and obeys $\operatorname{tr}(O^\dagger O)=d^N$. Alice measures $AC$; Bob selects the reported port and discards the others. Entanglement fidelities are tested against a normalized reference-input singlet, with no correction on the selected port.
--
--   For every port $i$, let $V_i$ insert the normalized $A_i,C$ singlet into a vector on the complementary ports. Then
--   $$V_i^\dagger\rho V_i=\frac{N+d^2-1}{d^{N+1}}I_{\bar A_i},\qquad V_i^\dagger(\operatorname{supp}\rho)V_i=I_{\bar A_i}.$$
--   These are identities of operators on the actual complement. At $N=1$ this space is one-dimensional and the first coefficient equals one. They supply the identities used in Appendix C's SRM fidelity bound; the unrestricted-scale squared inequality in its intermediate calculation is not asserted.
-- source:
--   Some remarks on port-based teleportation, arXiv:1506.01555v2, PDF p. 7, Appendix C Eq.(C1): singlet sandwiches of rho and its support

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P53

open scoped Classical ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

-- Accepted generic matrix and positive-operator interfaces. The support is the
-- orthogonal range projection; all uses below are on positive physical rho.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

/-- PDF p.7, Eq.(C1): operator-valued singlet sandwiches, including N=1.
No unrestricted-a squared lower bound from Eq.(C2) is asserted. -/
theorem singlet_sandwiches (d N : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N) (i : Fin N) :
    (singletInsert (d := d) i)ᴴ * pbtRho d N * singletInsert i =
      (((((N : ℝ) + (d : ℝ) ^ 2 - 1) / (d : ℝ) ^ (N + 1)) : ℝ) : ℂ) •
        (1 : Op (PortComplement d N i)) ∧
    (singletInsert (d := d) i)ᴴ * support (pbtRho d N) * singletInsert i =
      (1 : Op (PortComplement d N i)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P53

end
