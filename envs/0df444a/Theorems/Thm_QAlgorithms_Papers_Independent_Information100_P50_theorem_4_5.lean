-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_theorem_4_5
-- name    : QAlgorithms.Papers.Independent.Information100.P50.theorem_4_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:01:41.341351+00:00
-- url     : https://prove2.me/theorems/46df01a1-97af-40d4-9a57-5dc96f77a198
-- title:
--   Theorem 4.5: For CP pairs with the same sum Omega, fixed-frame derivatives T1,T2 and every Kubo–Ando mean sigma, diamond(Ph
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For a fixed linearly independent Kraus family $(V_k)_{k=1}^r$, put $\Omega(X)=\sum_k V_kXV_k^*$, $W=[\operatorname{vec}(V_1)\ \cdots\ \operatorname{vec}(V_r)]$, and $\Psi_T(X)=\sum_{k,l}T_{kl}V_kXV_l^*$. An effect $T$ determines the pair $(\Psi_T,\Psi_{I-T})$ with common sum $\Omega$. This parametrizes exactly the source's pairs and derivatives, by the ARN correspondence. All derivatives compared use this same family.
--
--   A Kubo–Ando mean $\sigma$ has a nonnegative operator-monotone representing function $f_\sigma$ with $f_\sigma(1)=1$. Set $g_\sigma(t)=t f_\sigma((1-t)/t)$ for $0<t<1$, $g_\sigma(0)=f_\sigma'(\infty)$, and $g_\sigma(1)=f_\sigma(0+)$. Matrix functions use spectral functional calculus and singular means use decreasing positive regularization.
--
--   For continuous $g:[0,1]\to\mathbb R$ and $\delta\ge0$, define the dimension-independent modulus
--
--   $$\omega_g(\delta)=\sup\{\|g(E)-g(E')\|_\infty:0\le E,E'\le I,\ \|E-E'\|_\infty\le\delta\},$$
--
--   where all finite matrix sizes occur. For any Kubo–Ando mean and effects $T_1,T_2$,
--
--   $$\|\Psi_{T_1}\sigma\Psi_{I-T_1}-\Psi_{T_2}\sigma\Psi_{I-T_2}\|_\diamond\le\|\Omega\|_\diamond\,\omega_{g_\sigma}(\|T_1-T_2\|_\infty).$$
--
--   This is a comparison only between splittings of one common sum.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 14, Theorem 4.5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Theorem 4.5, source PDF p.14. The modulus ranges over all finite dimensions. -/
theorem theorem_4_5 {dx dy r : ℕ}
    (s : Mean) (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (hV : LinearIndependent ℂ V)
    (T1 T2 : M r) (hT1 : IsEffect T1) (hT2 : IsEffect T2) :
    cbTraceNorm (cpMean s (arnFamily V T1) (arnFamily V (1 - T1)) -
      cpMean s (arnFamily V T2) (arnFamily V (1 - T2))) ≤
      cbTraceNorm (krausMap V) * operatorModulus (meanPerspective s) (specNorm (T1 - T2)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
