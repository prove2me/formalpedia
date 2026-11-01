-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P53_monogamy_asymptotic_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P53.monogamy_asymptotic_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:31:13.986261+00:00
-- url     : https://prove2.me/theorems/5534e6f5-912a-4aa8-8307-d03c49a31aa8
-- title:
--   Uniform fixed-d asymptotic fidelity upper bound
-- statement:
--   Let $N\ge1$ and $d\ge2$ be integers. Alice and Bob have $N$ ordered $d$-dimensional ports, and the input register $C$ has dimension $d$. Write $s=(d-1)/2$ and $|S\rangle=d^{-1/2}\sum_{m=-s}^s(-1)^{s-m}|s,m\rangle|s,-m\rangle$. Put $P_i=|S\rangle\langle S|_{A_iC}\otimes I_{\bar A_i}$, $\sigma_i=d^{-(N-1)}P_i$, and $\rho=\sum_i\sigma_i$. A resource filter $O$ gives $|\Psi_O\rangle=(O_A\otimes I_B)|S\rangle^{\otimes N}$ and obeys $\operatorname{tr}(O^\dagger O)=d^N$. Alice measures $AC$; Bob selects the reported port and discards the others. Entanglement fidelities are tested against a normalized reference-input singlet, with no correction on the selected port.
--
--   Fix $d\ge2$. There exist constants $C_d\ge0$ and $N_{0,d}\ge2$ such that for every $N\ge N_{0,d}$ and every normalized resource and deterministic POVM satisfying the section VI conditions $p_i=1/N$, equal correct-port fidelities and equal other-port fidelities, the actual entanglement fidelity satisfies
--   $$F\le1-\frac1{4(d-1)N^2}+\frac{C_d}{N^3}.$$
--   The constants are independent of $N$ and the protocol. The bound has the sign and leading coefficient of Eq.(28). This is the symmetric-port consequence derived using cloning monogamy; the cited background inequalities are not hypotheses, and no general symmetrization theorem is asserted.
-- source:
--   Some remarks on port-based teleportation, arXiv:1506.01555v2, PDF p. 5, VI Eqs.(26)-(28): asymptotic monogamy upper bound on deterministic fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P53

open scoped Classical ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

-- Accepted generic matrix and positive-operator interfaces. The support is the
-- orthogonal range projection; all uses below are on positive physical rho.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

/-- PDF p.5, Eq.(28): fixed-d symmetric-port bound. Constants precede N and
all protocols; cited cloning/isotropic results are not assumed as hypotheses. -/
theorem monogamy_asymptotic_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N →
      ∀ (O : Op (Ports d N)) (E : Fin N → Op (AC d N)) (Fother : ℝ),
        NormalizedResource O → DeterministicPOVM E → SymmetricPorts O E Fother →
        pbtFidelity O E ≤ 1 - 1 / (4 * ((d : ℝ) - 1) * (N : ℝ) ^ 2) +
          C / (N : ℝ) ^ 3 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P53

end
