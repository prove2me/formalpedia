-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_proposition_4_8
-- name    : QAlgorithms.Papers.Independent.Information100.P50.proposition_4_8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:03:43.901493+00:00
-- url     : https://prove2.me/theorems/f3e85bf6-28cc-4251-8614-c4103b9da742
-- title:
--   Proposition 4.8: For an independent Kraus family V_k of CP Omega with W=[vec(V_k)] and G=W*W, and arbitrary Hermitian T1,T2, la
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For a fixed linearly independent Kraus family $(V_k)_{k=1}^r$, put $\Omega(X)=\sum_k V_kXV_k^*$, $W=[\operatorname{vec}(V_1)\ \cdots\ \operatorname{vec}(V_r)]$, and $\Psi_T(X)=\sum_{k,l}T_{kl}V_kXV_l^*$. An effect $T$ determines the pair $(\Psi_T,\Psi_{I-T})$ with common sum $\Omega$. This parametrizes exactly the source's pairs and derivatives, by the ARN correspondence. All derivatives compared use this same family.
--
--   Let $G=W^*W$. For arbitrary Hermitian coefficient matrices $T_1,T_2$, if $r>0$ then
--
--   $$\frac{\lambda_{\min}(G)}{\dim X}\|T_1-T_2\|_1\le\|\Psi_{T_1}-\Psi_{T_2}\|_\diamond\le\|\Omega^*(I_Y)\|_\infty\|T_1-T_2\|_\infty.$$
--
--   The upper bound also holds when $r=0$; then both coefficient maps, the dominating map, and their completely bounded trace norms are zero. No minimum of an empty spectrum is asserted. Here $\|\cdot\|_1$ is the matrix trace norm. Coefficients need not be effects. This compares derivatives and maps in both directions.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 16, Proposition 4.8

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Proposition 4.8, source PDF p.16, visually checked: G=W*W and the lower coefficient
is lambda_min(G)/dim X. The empty Kraus case has zero maps and is stated separately. -/
theorem proposition_4_8 {dx dy r : ℕ} (hdx : 0 < dx) (hdy : 0 < dy)
    (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (hV : LinearIndependent ℂ V)
    (T1 T2 : M r) (hT1 : T1.IsHermitian) (hT2 : T2.IsHermitian) :
    (0 < r → minEigenvalue ((krausColumnMatrix V)ᴴ * krausColumnMatrix V) / (dx : ℝ) *
      traceNorm (T1 - T2) ≤ cbTraceNorm (arnFamily V T1 - arnFamily V T2)) ∧
    cbTraceNorm (arnFamily V T1 - arnFamily V T2) ≤
      specNorm (hilbertSchmidtAdjoint (krausMap V) 1) * specNorm (T1 - T2) ∧
    (r = 0 → arnFamily V T1 = 0 ∧ arnFamily V T2 = 0 ∧ krausMap V = 0 ∧
      cbTraceNorm (arnFamily V T1 - arnFamily V T2) = 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
