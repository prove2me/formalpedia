-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_theorem_4_6
-- name    : QAlgorithms.Papers.Independent.Information100.P50.theorem_4_6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:02:23.501501+00:00
-- url     : https://prove2.me/theorems/70aa25a9-763a-4a47-8c21-16ddd74cd389
-- title:
--   Theorem 4.6: geometric fidelity under a common ARN frame
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For a fixed linearly independent Kraus family $(V_k)_{k=1}^r$, put $\Omega(X)=\sum_k V_kXV_k^*$, $W=[\operatorname{vec}(V_1)\ \cdots\ \operatorname{vec}(V_r)]$, and $\Psi_T(X)=\sum_{k,l}T_{kl}V_kXV_l^*$. An effect $T$ determines the pair $(\Psi_T,\Psi_{I-T})$ with common sum $\Omega$. This parametrizes exactly the source's pairs and derivatives, by the ARN correspondence. All derivatives compared use this same family.
--
--   For two pairs $\Phi_i=\Psi_{T_i}$ and $\Psi_i=\Psi_{I-T_i}$, $i=1,2$, sharing the sum $\Omega$,
--
--   $$|\widehat F(\Phi_1,\Psi_1)-\widehat F(\Phi_2,\Psi_2)|\le\|\Omega^*(I_Y)\|_\infty\sqrt{\|T_1-T_2\|_\infty}.$$
--
--   Furthermore,
--
--   $$\|\Phi_1\#\Psi_1-\Phi_2\#\Psi_2\|_\diamond\le\|\Omega^*(I_Y)\|_\infty\sqrt{\|T_1-T_2\|_\infty}.$$
--
--   The fidelity $\widehat F$ is unsquared, optimized over one common bipartite density input. These are the paper's main common-sum continuity estimates.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 14, Theorem 4.6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Theorem 4.6 (the original seed node), source PDF pp.14–15, including furthermore. -/
theorem theorem_4_6 {dx dy r : ℕ} (hdx : 0 < dx) (hdy : 0 < dy)
    (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (hV : LinearIndependent ℂ V)
    (T1 T2 : M r) (hT1 : IsEffect T1) (hT2 : IsEffect T2) :
    |geometricFidelity (arnFamily V T1) (arnFamily V (1 - T1)) -
      geometricFidelity (arnFamily V T2) (arnFamily V (1 - T2))| ≤
      specNorm (hilbertSchmidtAdjoint (krausMap V) 1) * Real.sqrt (specNorm (T1 - T2)) ∧
    cbTraceNorm (cpGeometricMean (arnFamily V T1) (arnFamily V (1 - T1)) -
      cpGeometricMean (arnFamily V T2) (arnFamily V (1 - T2))) ≤
      specNorm (hilbertSchmidtAdjoint (krausMap V) 1) * Real.sqrt (specNorm (T1 - T2)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
