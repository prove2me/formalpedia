-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P40_bellProtocol_optimal
-- name    : QAlgorithms.Papers.Independent.Renew46.P40.bellProtocol_optimal
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:17:59.162707+00:00
-- url     : https://prove2.me/theorems/afc7d234-aa14-4e1e-9012-bc3fa7402b26
-- title:
--   Optimal Bell-measurement teleportation channel and attained mean fidelity
-- statement:
--   Let $n\geq1$ and $H=\mathbb C^n$ with computational basis $|0\rangle,\ldots,|n-1\rangle$. Set $\omega=e^{-2\pi i/n}$, $h|j\rangle=|(j+1)\bmod n\rangle$, $g|j\rangle=\omega^j|j\rangle$, and $U_{st}=h^tg^s$. All labels below range over $\{0,\ldots,n-1\}^2$. Write $\overline A$ for entrywise conjugation and $A^\dagger$ for adjoint. Define $|\Phi\rangle=n^{-1/2}\sum_j|jj\rangle$ and $|\Phi_m\rangle=(I\otimes\overline{U_m})|\Phi\rangle$.
--
--   Let $\chi$ be any positive semidefinite trace-one resource on $H\otimes H$, with Alice's half first. For a fixed family of unitary matrices $T=(T_m)_m$, define $\Lambda_\chi(T)$ operationally: independently prepare $\rho\otimes\chi$ on registers $1,2,3$; project registers $1,2$ onto the Bell basis, communicate outcome $m$, apply $T_m^\dagger$ on register $3$, trace out registers $1,2$, and sum the unnormalized branches. The correction family may depend on $\chi$ and the outcome but is independent of the unknown input.
--
--   For a unitary $W$ define $q_\chi(W)=\langle\Phi|(I\otimes W^\dagger)\chi(I\otimes W)|\Phi\rangle$, and let $\mathcal F(\chi)=\sup_{W\in U(n)}q_\chi(W)$ be the fully entangled fraction. A maximizing unitary exists. For every maximizing $W$, set $T_m^{\mathrm{opt}}=WU_m$ and $\Lambda_O=\Lambda_\chi(T^{\mathrm{opt}})$. This is a legal unitary correction family and $\Lambda_O$ is completely positive and trace preserving. With $c_{ab}=\langle\Phi_a|\chi|\Phi_b\rangle$, for every density input $\rho$,
--
--   $$
--   \Lambda_O(\rho)=\frac1{n^2}\sum_{a,b}c_{ab}\sum_m U_m^\dagger W^\dagger\overline{U_a}U_m\rho U_m^\dagger\overline{U_b}^{\dagger}WU_m.
--   $$
--
--   Writing $f_\chi(T)$ for the probability Haar mean of the pure-input survival fidelity, one has
--
--   $$
--   f_\chi(T)\leq f_\chi(T^{\mathrm{opt}})=\frac{n\mathcal F(\chi)}{n+1}+\frac1{n+1}
--   \qquad\text{for every unitary correction family }T.
--   $$
--
--   The theorem supplies an attained maximum for the fixed Bell-measurement protocol, describes the channel for every maximizing $W$, and asserts no uniqueness or optimization over arbitrary LOCC.
--
--   **Formalization Note** Printed Eq.(14) has the same resource-index conjugation error as Eq.(7). Precisely those factors are corrected above using Eq.(4), while Eq.(15) and $T_m^{\mathrm{opt}}=WU_m$ are preserved. The real supremum is over a nonempty compact unitary group and continuous overlap; attainment is a conclusion.
-- source:
--   Optimal Teleportation Based on Bell Measurement, arXiv:quant-ph/0208015v2, PDF p. 6, Theorem 3, Eqs.(14)-(15): optimal Bell-measurement channel and maximal mean fidelity (abstract seed)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P40

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Renew46.P40

/-- Theorem 3, Eqs.(14)–(15), PDF p.6 (announced p.1) of arXiv:quant-ph/0208015v2.
A maximizing W exists. Every maximizing W supplies a legal optimal correction family,
a CPTP operational channel, its explicit expansion, the achieved mean fidelity, and an
upper bound against every other unitary correction family for the same Bell measurement.
SOURCE CORRECTION (trap 30, Q11): Eq.(14)'s resource-index Weyl factors are conjugated
as forced by Eq.(4); see HARD.md. No optimization over arbitrary LOCC is asserted. -/
theorem bellProtocol_optimal (n : ℕ) (hn : 0 < n) (chi : ResourceMatrix n)
    (hchi : IsDensityMatrix chi) :
    (∃ W : Matrix.unitaryGroup (Fin n) ℂ,
      entangledOverlap hn chi (W : QuditMatrix n) = fullyEntangledFraction hn chi) ∧
    ∀ W : Matrix.unitaryGroup (Fin n) ℂ,
      entangledOverlap hn chi (W : QuditMatrix n) = fullyEntangledFraction hn chi →
        IsCorrectionFamily (optimalCorrections W) ∧
        IsChannel (teleportation hn chi (optimalCorrections W)) ∧
        (∀ rho : QuditMatrix n, IsDensityMatrix rho →
          teleportation hn chi (optimalCorrections W) rho = optimalExpansion hn chi W rho) ∧
        QuditFidelity.averageFidelity n hn (teleportation hn chi (optimalCorrections W)) =
          (n : ℝ) * fullyEntangledFraction hn chi / ((n : ℝ) + 1) +
            1 / ((n : ℝ) + 1) ∧
        (∀ T : BellLabel n → QuditMatrix n, IsCorrectionFamily T →
          QuditFidelity.averageFidelity n hn (teleportation hn chi T) ≤
            QuditFidelity.averageFidelity n hn (teleportation hn chi (optimalCorrections W))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P40

end
