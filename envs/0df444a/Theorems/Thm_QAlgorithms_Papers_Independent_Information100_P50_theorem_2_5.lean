-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_theorem_2_5
-- name    : QAlgorithms.Papers.Independent.Information100.P50.theorem_2_5
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:51:43.580229+00:00
-- url     : https://prove2.me/theorems/74af12ed-82bf-4406-80f2-cca5eb29df97
-- title:
--   Theorem 2.5: For Hermitian T, Psi_T(X)=Tr_Z((I_Y tensor T^transpose) S X S*); tr(Psi_T(X))=tr(T^transpose Phi^c(X)); Psi_T^
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For a fixed linearly independent Kraus family $(V_k)_{k=1}^r$, put $\Omega(X)=\sum_k V_kXV_k^*$, $W=[\operatorname{vec}(V_1)\ \cdots\ \operatorname{vec}(V_r)]$, and $\Psi_T(X)=\sum_{k,l}T_{kl}V_kXV_l^*$. An effect $T$ determines the pair $(\Psi_T,\Psi_{I-T})$ with common sum $\Omega$. This parametrizes exactly the source's pairs and derivatives, by the ARN correspondence. All derivatives compared use this same family.
--
--   Let $Sx=\sum_k V_kx\otimes e_k$ and $\Omega^c(X)=\operatorname{Tr}_Y(SXS^*)$. For every Hermitian coefficient matrix $T$ and every $X$,
--
--   $$\Psi_T(X)=\operatorname{Tr}_Z((I_Y\otimes T^\top)SXS^*),\quad \operatorname{tr}\Psi_T(X)=\operatorname{tr}(T^\top\Omega^c(X)),\quad \Psi_T^*(I_Y)=S^*(I_Y\otimes T^\top)S=(\Omega^c)^*(T^\top).$$
--
--   For an effect $T$, this is a CP submap interpreted as an environmental measurement outcome. Every finite environmental POVM $(T_i^\top)$ decomposes a channel $\Omega$ as $\sum_i\Psi_{T_i}$, with each branch CP. If $T\ge0$, its induced trace norm equals its completely bounded trace norm and
--
--   $$\|\Psi_T\|_\diamond=\max_{\rho\in\mathcal D(X)}\operatorname{tr}(T^\top\Omega^c(\rho)).$$
--
--   The maximum is attained. Here $\mathcal D(X)$ consists of PSD matrices of trace one; $T^\top$ is ordinary transpose. This identifies ARN coefficients with environmental effects.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 4, Theorem 2.5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Theorem 2.5, source PDF pp.4–5. Hermitian T is not required to be an effect;
the effect interpretation and positive-T norm formula are separate clauses. -/
theorem theorem_2_5 {dx dy r : ℕ} (hdx : 0 < dx) (hdy : 0 < dy)
    (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (hV : LinearIndependent ℂ V)
    (T : M r) (hT : T.IsHermitian) :
    (∀ X : M dx,
      arnFamily V T X = traceRight
        (((1 : M dy) ⊗ₖ T.transpose) * stinespringOperator V * X * (stinespringOperator V)ᴴ) ∧
      (arnFamily V T X).trace = (T.transpose * complementaryMap V X).trace) ∧
    hilbertSchmidtAdjoint (arnFamily V T) 1 =
      (stinespringOperator V)ᴴ * ((1 : M dy) ⊗ₖ T.transpose) * stinespringOperator V ∧
    hilbertSchmidtAdjoint (arnFamily V T) 1 =
      hilbertSchmidtAdjoint (complementaryMap V) T.transpose ∧
    (IsEffect T → cpOrder (arnFamily V T) (krausMap V)) ∧
    (IsChannel (krausMap V) → ∀ (m : ℕ) (Ti : Fin m → M r),
      (∀ i, (Ti i).transpose.PosSemidef) → (∑ i, (Ti i).transpose) = 1 →
      (∀ i, Entanglement.IsCompletelyPositive (arnFamily V (Ti i))) ∧
      (∑ i, arnFamily V (Ti i)) = krausMap V) ∧
    (T.PosSemidef → inducedNorm 1 (arnFamily V T) = cbTraceNorm (arnFamily V T) ∧
      ∃ rho : M dx, IsDensityMatrix rho ∧
        cbTraceNorm (arnFamily V T) = (T.transpose * complementaryMap V rho).trace.re ∧
        ∀ tau : M dx, IsDensityMatrix tau →
          (T.transpose * complementaryMap V tau).trace.re ≤
            (T.transpose * complementaryMap V rho).trace.re) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
