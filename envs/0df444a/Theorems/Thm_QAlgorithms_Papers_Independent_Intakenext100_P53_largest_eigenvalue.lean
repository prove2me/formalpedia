-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P53_largest_eigenvalue
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P53.largest_eigenvalue
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:28:00.301995+00:00
-- url     : https://prove2.me/theorems/57436f09-b98a-4878-99a0-2710feba13d3
-- title:
--   Exact largest eigenvalue of the physical signal sum
-- statement:
--   Let $N\ge1$ and $d\ge2$ be integers. Alice and Bob have $N$ ordered $d$-dimensional ports, and the input register $C$ has dimension $d$. Write $s=(d-1)/2$ and $|S\rangle=d^{-1/2}\sum_{m=-s}^s(-1)^{s-m}|s,m\rangle|s,-m\rangle$. Put $P_i=|S\rangle\langle S|_{A_iC}\otimes I_{\bar A_i}$, $\sigma_i=d^{-(N-1)}P_i$, and $\rho=\sum_i\sigma_i$. A resource filter $O$ gives $|\Psi_O\rangle=(O_A\otimes I_B)|S\rangle^{\otimes N}$ and obeys $\operatorname{tr}(O^\dagger O)=d^N$. Alice measures $AC$; Bob selects the reported port and discards the others. Entanglement fidelities are tested against a normalized reference-input singlet, with no correction on the selected port.
--
--   The exact largest eigenvalue is
--   $$\lambda_{\max}(\rho)=\frac{N+d-1}{d^N}.$$
--   More explicitly, $\rho\preceq((N+d-1)/d^N)I$. Insert a singlet into each pair $A_i,C$ and put every complementary spin in its highest-weight state. The normalized equal-amplitude sum $v$ of these $N$ vectors is a unit eigenvector attaining this bound and has total spin $(N-1)s$. The definition normalizes its constructed vector rather than assuming a maximizing state as input. This gives both the bound and attainment, including $\lambda_{\max}=1$ at $N=1$.
-- source:
--   Some remarks on port-based teleportation, arXiv:1506.01555v2, PDF p. 2, II Eq.(9), Appendix A: exact largest eigenvalue of rho

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P53

open scoped Classical ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

-- Accepted generic matrix and positive-operator interfaces. The support is the
-- orthogonal range projection; all uses below are on positive physical rho.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

/-- PDF p.2, Eq.(9), p.6: exact maximum and the source's explicit
maximum-spin attaining vector with equal port amplitudes. -/
theorem largest_eigenvalue (d N : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N) :
    let L : ℝ := ((N : ℝ) + d - 1) / (d : ℝ) ^ N
    ((L : ℂ) • (1 : Op (AC d N)) - pbtRho d N).PosSemidef ∧
    QAlgorithms.IsState (maximumSpinVector d N) ∧
    QAlgorithms.act (pbtRho d N) (maximumSpinVector d N) = (L : ℂ) • maximumSpinVector d N ∧
    QAlgorithms.act (totalCasimir d N) (maximumSpinVector d N) =
      (((((N : ℝ) - 1) * ((d : ℝ) - 1) / 2) *
        (((N : ℝ) - 1) * ((d : ℝ) - 1) / 2 + 1) : ℝ) : ℂ) • maximumSpinVector d N := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P53

end
