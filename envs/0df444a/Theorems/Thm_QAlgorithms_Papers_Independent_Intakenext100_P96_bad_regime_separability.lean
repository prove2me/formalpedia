-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P96_bad_regime_separability
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P96.bad_regime_separability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:52:08.898982+00:00
-- url     : https://prove2.me/theorems/cec2a55b-e3b7-4352-8236-66a5d818e39a
-- title:
--   Both returned states are separable in the bad regime
-- statement:
--   Work in the retained vacuum/single-photon model, on a signal space with vacuum $|\mathrm{vac}\rangle$ and $d\ge1$ orthogonal single-photon modes. Let $b\ge0$ be the background probability per mode, with $db\le1$, and let $0\le\eta\le1$ be the reflection probability. Set
--   $$
--   \rho_0=(1-db)|\mathrm{vac}\rangle\langle\mathrm{vac}|+b\sum_{k=1}^d|k\rangle\langle k|.
--   $$
--
--   Use the resource $|\Phi_d\rangle=d^{-1/2}\sum_{k=1}^d|k\rangle_S|k\rangle_A$, transmitting only the signal and retaining the ancillary photon perfectly. Write $P_\Phi=|\Phi_d\rangle\langle\Phi_d|$, $\sigma_0=\rho_0\otimes I_A/d$, and $\sigma_1=(1-\eta)\sigma_0+\eta P_\Phi$.
--   In the bad regime $\eta d<b$ (equivalently $\eta d/b<1$, since this condition forces $b>0$), both returned states are normalized and separable across signal and ancilla:
--   $$
--   \sigma_j=\sum_{\ell=1}^{m_j}w_{j\ell}\,
--    a_{j\ell}\otimes c_{j\ell}\qquad (j=0,1),
--   $$
--   where $m_j$ is finite, $w_{j\ell}\ge0$, $\sum_\ell w_{j\ell}=1$, and every $a_{j\ell}$ and $c_{j\ell}$ is a positive trace-one density operator on the appropriate subsystem.
--
--   This states actual separability of the specified returned pair, even though its ideal joint detector still has the background acceptance probability $b/d$. It makes no arbitrary-input entanglement-breaking claim.
-- source:
--   Quantum Illumination, arXiv:0803.2022v2, PDF p. 8, Unnumbered: no signal–ancilla entanglement survives in the bad regime

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P96

noncomputable section

open Filter

open scoped BigOperators Topology ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P96

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.8--9: in the bad regime eta*d/b<1, the returned pair is a separable
normalized density. The conclusion is finite convex-product separability,
not merely positivity of the partial transpose. -/
theorem bad_regime_separability (p : ModelParameters)
    (hbad : p.eta * (p.d : ℝ) < p.b) :
    (IsDensityMatrix (pairAbsent p.d p.b) ∧
      QAlgorithms.Entanglement.IsSeparablePositive (pairAbsent p.d p.b)) ∧
    (IsDensityMatrix (pairPresent p.d p.b p.eta) ∧
      QAlgorithms.Entanglement.IsSeparablePositive (pairPresent p.d p.b p.eta)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P96

end
