-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P19_symmetric_canonical_pgm_optimal
-- name    : QAlgorithms.Papers.Independent.Extend50.P19.symmetric_canonical_pgm_optimal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:06:40.360529+00:00
-- url     : https://prove2.me/theorems/1fba9d72-d021-47c0-8b59-ce7aa6105023
-- title:
--   The original PGM is optimal for every symmetric canonical port resource
-- statement:
--   Let $d,N\ge1$ be integers. Write $\Phi^+=|\Phi^+\rangle\langle\Phi^+|$, where $|\Phi^+\rangle=d^{-1/2}\sum_{j=1}^d|j,j\rangle$, and let $\varphi_0=(\Phi^+)^{\otimes N}$ be the port resource. On $A^N B$, define $\rho_i=\Phi^+_{A_iB}\otimes I_{A_i^c}/d^{N-1}$, $\bar\rho=\sum_i\rho_i$, and $\Pi$ as the support projection of $\bar\rho$. All inverse powers are generalized spectral inverse powers, zero on the kernel. The fixed measurement is
--
--   $$E_i^0=\bar\rho^{-1/2}\rho_i\bar\rho^{-1/2}+\frac{I-\Pi}{N}.$$
--
--   The complementary term completes the PGM to a full POVM without affecting the ensemble probabilities. Let $p(\rho,E)=N^{-1}\sum_i\operatorname{tr}(E_i\rho_i)$. Let $F(\varphi,E)$ denote the entanglement fidelity of deterministic single-input PBT: Alice measures $A_0A^N$ with the $N$-outcome POVM $E$, communicates $i$, and Bob keeps $B_i$ as the output and traces out his other ports. Thus $F=\langle\Phi^+|(\Lambda\otimes\mathrm{id})(\Phi^+)|\Phi^+\rangle$ for the resulting physical channel $\Lambda$.
--
--   For each partition $\mu\vdash_d N$, let $P_\mu$ be the full physical Schur isotypic projector, $m_{d,\mu}=\dim V_\mu^d$, and $d_\mu=\dim W_\mu$. A coefficient family $c=(c_\mu)$ is feasible when
--
--   $$c_\mu\ge0,\qquad\sum_{\mu\vdash_d N}c_\mu d_\mu m_{d,\mu}=d^N.$$
--
--   Define $O_c=\sum_\mu\sqrt{c_\mu}P_\mu$, $|\varphi_c\rangle=(O_c\otimes I)|\Phi^+\rangle^{\otimes N}$, and $\varphi_c=|\varphi_c\rangle\langle\varphi_c|$. Feasibility makes this a density operator. Its discrimination ensemble is $\eta_i^c=(O_c\otimes I_B)\rho_i(O_c\otimes I_B)^\dagger$.
--
--   The measurement $E^0$ is fixed independently of $c$. For every feasible $c$ and every $N$-outcome POVM $E$,
--
--   $$p(\eta^c,E)\le p(\eta^c,E^0),\qquad F(\varphi_c,E)\le F(\varphi_c,E^0).$$
--
--   Thus the PGM constructed from the original maximally entangled ensemble is optimal pointwise throughout the symmetric canonical family, including resources with zero coefficients.
--
--   For every feasible $c$, the exact attained values are
--
--   $$p(\eta^c,E^0)=\frac{1}{Nd^N}\sum_{\alpha\vdash_d N-1}\left(\sum_{\mu=\alpha+\square}\sqrt{c_\mu d_\mu m_{d,\mu}}\right)^2,$$
--   $$F(\varphi_c,E^0)=\frac{1}{d^{N+2}}\sum_{\alpha\vdash_d N-1}\left(\sum_{\mu=\alpha+\square}\sqrt{c_\mu d_\mu m_{d,\mu}}\right)^2.$$
--
--   These pointwise formulas hold before maximizing over resource coefficients.
-- source:
--   Optimality of the pretty good measurement for port-based teleportation, arXiv:2008.11194v2, PDF p. 14, §§5.1-5.2, (5.10)-(5.11), (5.23), and optimality conclusion on p.15

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P19

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Extend50.P19

attribute [local instance] Classical.propDecidable

/-- Sections 5.1-5.2, PDF pp.12-15: the SAME original PGM optimizes each
symmetric canonical resource, with the exact success and fidelity from
(5.10)-(5.11), (5.23), and (3.7). It is fixed before c and allows c_mu=0.
No inverse-Gram assertion for a vanished chi vector is used as a hypothesis. -/
theorem symmetric_canonical_pgm_optimal (d N : ℕ) (hd : 0 < d) (hN : 0 < N) :
    IsPOVM (standardPGM d N) ∧
    ∀ c : Schur.Partition d N → ℝ, FeasibleWeights c →
      IsDensityMatrix (canonicalResource c) ∧
      discriminationSuccess (canonicalEnsemble c) (standardPGM d N) =
        coefficientScore c / ((N : ℝ) * (d : ℝ)^N) ∧
      pbtFidelity (canonicalResource c) (standardPGM d N) =
        coefficientScore c / (d : ℝ)^(N+2) ∧
      ∀ E : Fin N → Matrix (DiscriminationIndex d N) (DiscriminationIndex d N) ℂ,
        IsPOVM E →
        discriminationSuccess (canonicalEnsemble c) E ≤
          discriminationSuccess (canonicalEnsemble c) (standardPGM d N) ∧
        pbtFidelity (canonicalResource c) E ≤
          pbtFidelity (canonicalResource c) (standardPGM d N) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P19

end
