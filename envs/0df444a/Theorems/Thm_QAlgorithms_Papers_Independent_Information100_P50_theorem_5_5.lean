-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_theorem_5_5
-- name    : QAlgorithms.Papers.Independent.Information100.P50.theorem_5_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:04:50.375142+00:00
-- url     : https://prove2.me/theorems/7c7bb81e-3681-4c75-9e51-6b1ae535eeb0
-- title:
--   Theorem 5.5: For 0<alpha<1 and CP pairs with common sum Omega and common-frame derivatives T1,T2, |Qhat_alpha(Phi1||Psi1)-Q
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For a fixed linearly independent Kraus family $(V_k)_{k=1}^r$, put $\Omega(X)=\sum_k V_kXV_k^*$, $W=[\operatorname{vec}(V_1)\ \cdots\ \operatorname{vec}(V_r)]$, and $\Psi_T(X)=\sum_{k,l}T_{kl}V_kXV_l^*$. An effect $T$ determines the pair $(\Psi_T,\Psi_{I-T})$ with common sum $\Omega$. This parametrizes exactly the source's pairs and derivatives, by the ARN correspondence. All derivatives compared use this same family.
--
--   For $0<\alpha<1$ and the two common-sum pairs $\Phi_i=\Psi_{T_i}$, $\Psi_i=\Psi_{I-T_i}$,
--
--   $$|\widehat Q_\alpha(\Phi_1\|\Psi_1)-\widehat Q_\alpha(\Phi_2\|\Psi_2)|\le\|\Omega^*(I_Y)\|_\infty\left(\|T_1-T_2\|_\infty^\alpha+\|T_1-T_2\|_\infty^{1-\alpha}\right).$$
--
--   Here $\widehat Q_\alpha$ is the infimum of the regularized output-state perspective $\operatorname{tr}(B\#_\alpha A)$ over one common bipartite density input, with $A$ the first map's output and $B$ the second map's output. This controls the quasi-entropy, rather than its possibly infinite logarithmic divergence.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 18, Theorem 5.5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Theorem 5.5, source PDF pp.18–19. This controls Qhat, not its possibly infinite logarithm. -/
theorem theorem_5_5 {dx dy r : ℕ} (hdx : 0 < dx) (hdy : 0 < dy)
    (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (hV : LinearIndependent ℂ V)
    (T1 T2 : M r) (hT1 : IsEffect T1) (hT2 : IsEffect T2)
    (alpha : ℝ) (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    |renyiQ alpha (arnFamily V T1) (arnFamily V (1 - T1)) -
      renyiQ alpha (arnFamily V T2) (arnFamily V (1 - T2))| ≤
      specNorm (hilbertSchmidtAdjoint (krausMap V) 1) *
        (Real.rpow (specNorm (T1 - T2)) alpha + Real.rpow (specNorm (T1 - T2)) (1 - alpha)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
