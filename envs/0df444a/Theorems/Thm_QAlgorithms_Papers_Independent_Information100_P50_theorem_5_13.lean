-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_theorem_5_13
-- name    : QAlgorithms.Papers.Independent.Information100.P50.theorem_5_13
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:07:59.808926+00:00
-- url     : https://prove2.me/theorems/2f963bb5-4072-4ebe-829b-49857e19f066
-- title:
--   Theorem 5.13: For bounded endpoint operator-convex f with f(1)=0, define h_f(t)=(1-t)f(t/(1-t)) for 0<t<1, h_f(0)=f(0+), h_f
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For a fixed linearly independent Kraus family $(V_k)_{k=1}^r$, put $\Omega(X)=\sum_k V_kXV_k^*$, $W=[\operatorname{vec}(V_1)\ \cdots\ \operatorname{vec}(V_r)]$, and $\Psi_T(X)=\sum_{k,l}T_{kl}V_kXV_l^*$. An effect $T$ determines the pair $(\Psi_T,\Psi_{I-T})$ with common sum $\Omega$. This parametrizes exactly the source's pairs and derivatives, by the ARN correspondence. All derivatives compared use this same family.
--
--   Let $f:(0,\infty)\to\mathbb R$ be operator convex in every matrix size, with $f(1)=0$ and finite real limits $a=f(0+)$ and $b=\lim_{t\to\infty}f(t)/t$. The maximal divergence $\widehat D_f$ is defined independently by the regularized state perspective and a supremum over a common bipartite density input. Outputs are not required to have trace one.
--
--   Define $h_f(t)=(1-t)f(t/(1-t))$ for $0<t<1$, with $h_f(0)=a$ and $h_f(1)=b$. This function is continuous on $[0,1]$. For every effect $T$,
--
--   $$\widehat D_f(\Psi_T\|\Psi_{I-T})=\lambda_{\max}\!\left(\operatorname{Tr}_Y(Wh_f(T)W^*)\right).$$
--
--   For any two effects $T_1,T_2$,
--
--   $$|\widehat D_f(\Psi_{T_1}\|\Psi_{I-T_1})-\widehat D_f(\Psi_{T_2}\|\Psi_{I-T_2})|\le\|\Omega^*(I_Y)\|_\infty\omega_{h_f}(\|T_1-T_2\|_\infty),\qquad\omega_{h_f}(\delta)\to0\ (\delta\downarrow0).$$
--
--   The modulus is the supremum over effects in all finite dimensions. Both the spectral identity and the continuity bound are conclusions.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 22, Theorem 5.13

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Theorem 5.13, source PDF pp.22–23, parts (a) and (b). The divergence is defined
by an input-state supremum, so the spectral formula is a conclusion. PDF p.22
visually confirms the absolute value in (b). -/
theorem theorem_5_13 {dx dy r : ℕ} (hdx : 0 < dx) (hdy : 0 < dy)
    (f : BoundedGenerator) (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ)
    (hV : LinearIndependent ℂ V) :
    convexPerspective f.f 0 = atZero f.f ∧ convexPerspective f.f 1 = atInfinity f.f ∧
    ContinuousOn (convexPerspective f.f) (Icc 0 1) ∧
    (∀ T : M r, IsEffect T →
      channelDivergence f.f (arnFamily V T) (arnFamily V (1 - T)) =
        maxEigenvalue (traceLeft
          (krausColumnMatrix V * cfc (convexPerspective f.f) T * (krausColumnMatrix V)ᴴ))) ∧
    (∀ T1 T2 : M r, IsEffect T1 → IsEffect T2 →
      |channelDivergence f.f (arnFamily V T1) (arnFamily V (1 - T1)) -
        channelDivergence f.f (arnFamily V T2) (arnFamily V (1 - T2))| ≤
        specNorm (hilbertSchmidtAdjoint (krausMap V) 1) *
          operatorModulus (convexPerspective f.f) (specNorm (T1 - T2))) ∧
    Tendsto (operatorModulus (convexPerspective f.f)) (𝓝[≥] (0 : ℝ)) (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
