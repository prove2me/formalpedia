-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_lemma_4_1
-- name    : QAlgorithms.Papers.Independent.Information100.P50.lemma_4_1
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:59:15.03762+00:00
-- url     : https://prove2.me/theorems/1fc98e29-6cb6-486b-8a26-3ebcc5d4be3b
-- title:
--   Lemma 4.1: For effects T1,T2 in the same independent Kraus decomposition of CP Phi, diamond(Psi_T1-Psi_T2)≤diamond(Psi_|T
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For a fixed linearly independent Kraus family $(V_k)_{k=1}^r$, put $\Omega(X)=\sum_k V_kXV_k^*$, $W=[\operatorname{vec}(V_1)\ \cdots\ \operatorname{vec}(V_r)]$, and $\Psi_T(X)=\sum_{k,l}T_{kl}V_kXV_l^*$. An effect $T$ determines the pair $(\Psi_T,\Psi_{I-T})$ with common sum $\Omega$. This parametrizes exactly the source's pairs and derivatives, by the ARN correspondence. All derivatives compared use this same family.
--
--   For effects $T_1,T_2$ in one ARN frame,
--
--   $$\|\Psi_{T_1}-\Psi_{T_2}\|_\diamond\le\|\Psi_{|T_1-T_2|}\|_\diamond\le\|\Omega\|_\diamond\|T_1-T_2\|_\infty.$$
--
--   The absolute value is the Hermitian operator absolute value, rather than an entrywise operation. Both estimates are retained; the middle positive map gives the sharper bound.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 12, Lemma 4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Lemma 4.1, source PDF pp.12–13. Both estimates, using one common Kraus family. -/
theorem lemma_4_1 {dx dy r : ℕ}
    (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (hV : LinearIndependent ℂ V)
    (T1 T2 : M r) (hT1 : IsEffect T1) (hT2 : IsEffect T2) :
    cbTraceNorm (arnFamily V T1 - arnFamily V T2) ≤
      cbTraceNorm (arnFamily V (hermitianAbsoluteValue (T1 - T2))) ∧
    cbTraceNorm (arnFamily V (hermitianAbsoluteValue (T1 - T2))) ≤
      cbTraceNorm (krausMap V) * specNorm (T1 - T2) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
