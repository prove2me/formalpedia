-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P19_port_average_spectrum
-- name    : QAlgorithms.Papers.Independent.Extend50.P19.port_average_spectrum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:05:22.717688+00:00
-- url     : https://prove2.me/theorems/92941ea3-fcd0-4770-ba7b-d486399632b7
-- title:
--   Spectrum and physical block multiplicities of the unnormalized port ensemble sum
-- statement:
--   Let $d,N\ge1$ be integers, and let $\rho_i=\Phi^+_{A_iB}\otimes I_{A_i^c}/d^{N-1}$, where $\Phi^+$ is the normalized maximally entangled state in the fixed computational basis. Set $\bar\rho=\sum_{i=1}^N\rho_i$, without dividing by $N$. For a valid partition $\nu$, write $m_{d,\nu}=\dim V_\nu^d$ and $d_\nu=\dim W_\nu$ for the actual Weyl and Specht dimensions. Let $P_\mu$ be the full $S_N$ isotypic projection on $A^N$, and let $Q_\alpha$ be the physical $U_d$ isotypic projection of type $V_\alpha^d$ for the action $U^{\otimes N}\otimes\overline U$ on $A^NB$. Then
--
--   $$\bar\rho=\sum_{\alpha\vdash_d N-1}\ \sum_{\mu=\alpha+\square}r_{\mu,\alpha}(P_\mu\otimes I_B)Q_\alpha,\qquad r_{\mu,\alpha}=\frac{N}{d^N}\frac{m_{d,\mu}d_\alpha}{m_{d,\alpha}d_\mu}.$$
--
--   For each displayed pair, the joint block $(P_\mu\otimes I_B)Q_\alpha$ has rank $m_{d,\alpha}d_\mu$. The equality holds on the full physical space, so the omitted sectors have zero action. It gives both eigenvalues and their representation-theoretic multiplicities, with no requirement $d\ge N$.
--
--   **Formalization Note** The mixed isotypic subspace is constructed as the span of images of all intertwining maps from the accepted polynomial Schur module; it is independent of $\bar\rho$ and its spectrum.
-- source:
--   Optimality of the pretty good measurement for port-based teleportation, arXiv:2008.11194v2, PDF p. 7, Lemma 3, (4.9)-(4.10)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P19

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Extend50.P19

attribute [local instance] Classical.propDecidable

/-- Lemma 3, PDF p.7, (4.9)-(4.10), attributed there to Studzinski et al.
and Christandl et al. Full-space equality makes all other mixed sectors zero;
the second clause retains the stated nonzero-block multiplicities. -/
theorem port_average_spectrum (d N : ℕ) (hd : 0 < d) (hN : 0 < N) :
    portAverage d N =
      (∑ alpha : Schur.Partition d (N-1), ∑ mu : Schur.Partition d N,
        if AddsBox alpha mu then (portEigenvalue alpha mu : ℂ) • mixedBlock alpha mu
        else 0) ∧
    ∀ (alpha : Schur.Partition d (N-1)) (mu : Schur.Partition d N), AddsBox alpha mu →
      Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin (mixedBlock alpha mu))) =
        weylDim alpha * spechtDim mu := by sorry

end QAlgorithms.Papers.Independent.Extend50.P19

end
