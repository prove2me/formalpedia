-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P27_isotropic_entanglement_assisted
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P27.isotropic_entanglement_assisted
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:16:33.599441+00:00
-- url     : https://prove2.me/theorems/e615ab45-b9ca-4410-8101-d42b4ced47a4
-- title:
--   Exact entanglement-assisted isotropic-qubit curve
-- statement:
--   Consider the memoryless maximally mixed qubit source $I/2$, with the Bell purification $\Phi_{RA}$ and fidelity-distortion observable $I-\Phi_{RA}$. Let $R^q_{\mathrm{ea}}(D)$ be its operational quantum rate-distortion function with unlimited prior entanglement and no free classical side channel. For $0\le D\le1$,
--
--   $$R^q_{\mathrm{ea}}(D)=\begin{cases}1-\tfrac12 H(1-D,D/3,D/3,D/3),&D\le3/4,\\0,&D>3/4.\end{cases}$$
--
--   Here $H(p)=-\sum_i p_i\log_2p_i$, with $0\log_2 0=0$. The branches agree at $D=3/4$.
--
--   This gives an exact assisted curve, with rate one at zero distortion and zero from distortion $3/4$ onward.
-- source:
--   Quantum rate distortion coding with auxiliary resources, arXiv:1212.5316v3, PDF p. 8, Theorem 11

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P27

open Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P19
  (first marginalRB mutualInformation bipartiteBlock epr)

open QAlgorithms.Papers.Independent.Information100.P08 (formation)

open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)

open QAlgorithms.Papers.Independent.Bridge50.P37 (isotropicState normalizedEntangledProjection)

/-- PDF pp.8--9, Theorem 11: exact isotropic-qubit assisted curve. The Bell
purification and fidelity observable are pinned by equalities, not postulated
entropy values. The two branches agree at D=3/4. The p.9 proof's 'fidelity p'
is a typo; for its Pauli channel fidelity is 1-p and distortion is p. -/
theorem isotropic_entanglement_assisted
    (S : DistortionSource (Fin 2) (Fin 2))
    (hsource : pureDensity S.psi = epr 2)
    (hdelta : S.delta = 1 - epr 2)
    (D : ℝ) (hD0 : 0 ≤ D) (hD1 : D ≤ 1) :
    rateDistortion S .entanglement D =
      ENNReal.ofReal (if D ≤ 3 / 4 then 1 - isotropicEntropy D / 2 else 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P27

end
