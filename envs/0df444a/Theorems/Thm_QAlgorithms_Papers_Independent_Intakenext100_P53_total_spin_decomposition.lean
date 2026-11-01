-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P53_total_spin_decomposition
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P53.total_spin_decomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:27:19.956239+00:00
-- url     : https://prove2.me/theorems/38a79b48-a3f9-442c-b03c-7150b53a8206
-- title:
--   Physical total-spin decomposition of the signal sum
-- statement:
--   Let $N\ge1$ and $d\ge2$ be integers. Alice and Bob have $N$ ordered $d$-dimensional ports, and the input register $C$ has dimension $d$. Write $s=(d-1)/2$ and $|S\rangle=d^{-1/2}\sum_{m=-s}^s(-1)^{s-m}|s,m\rangle|s,-m\rangle$. Put $P_i=|S\rangle\langle S|_{A_iC}\otimes I_{\bar A_i}$, $\sigma_i=d^{-(N-1)}P_i$, and $\rho=\sum_i\sigma_i$. A resource filter $O$ gives $|\Psi_O\rangle=(O_A\otimes I_B)|S\rangle^{\otimes N}$ and obeys $\operatorname{tr}(O^\dagger O)=d^N$. Alice measures $AC$; Bob selects the reported port and discards the others. Entanglement fidelities are tested against a normalized reference-input singlet, with no correction on the selected port.
--
--   Let $P_{\bar A_i}(j)$ be the spectral projector of the physical complementary-register squared angular momentum onto eigenvalue $j(j+1)$, and define
--   $$\rho_j=d^{-(N-1)}\sum_i |S\rangle\langle S|_{A_iC}\otimes P_{\bar A_i}(j).$$
--   Then $\rho=\sum_j\rho_j$. Each $\rho_j$ is supported on the actual total-spin-$j$ sector of $AC$ and commutes with the total $z$ component. For $j\ne j'$, $\rho_j\rho_{j'}=0$, hence its trace is zero. Only $j\le(N-1)s$ with the physical parity can occur. Impossible sectors have zero projectors; at $N=1$ the complement is the one-dimensional spin-zero vacuum. This is total-spin block diagonality, without an additional $S_A$ claim for general $d$.
-- source:
--   Some remarks on port-based teleportation, arXiv:1506.01555v2, PDF p. 2, II, Eqs.(7)-(8): total-spin block decomposition of rho

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P53

open scoped Classical ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

-- Accepted generic matrix and positive-operator interfaces. The support is the
-- orthogonal range projection; all uses below are on positive physical rho.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

/-- PDF p.2, Eqs.(7)-(8): full physical spin decomposition. The vacuum
complement at N=1 has spin zero. No S_A block diagonality is claimed for d>2. -/
theorem total_spin_decomposition (d N : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N) :
    pbtRho d N = ∑ t ∈ Finset.range ((N - 1) * (d - 1) + 1), rhoSpinBlock d N t ∧
    (∀ t : ℕ,
      casimirProjector (totalCasimir d N) t * rhoSpinBlock d N t = rhoSpinBlock d N t ∧
      rhoSpinBlock d N t * casimirProjector (totalCasimir d N) t = rhoSpinBlock d N t ∧
      totalComponent d N (quditSpinZ d) * rhoSpinBlock d N t =
        rhoSpinBlock d N t * totalComponent d N (quditSpinZ d)) ∧
    (∀ t u : ℕ, t ≠ u → rhoSpinBlock d N t * rhoSpinBlock d N u = 0 ∧
      Matrix.trace (rhoSpinBlock d N t * rhoSpinBlock d N u) = 0) ∧
    (∀ t : ℕ, (N - 1) * (d - 1) < t ∨ t % 2 ≠ ((N - 1) * (d - 1)) % 2 →
      rhoSpinBlock d N t = 0) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P53

end
