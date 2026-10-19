-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_theorem_2_13
-- name    : QAlgorithms.Papers.Independent.Information100.P50.theorem_2_13
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:52:25.422446+00:00
-- url     : https://prove2.me/theorems/b737d49e-1fff-4d35-8840-68a526e4e8ab
-- title:
--   Theorem 2.13: For every Kubo–Ando mean sigma and CP pair Phi,Psi with Omega=Phi+Psi and fixed independent Kraus matrix W and
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For a fixed linearly independent Kraus family $(V_k)_{k=1}^r$, put $\Omega(X)=\sum_k V_kXV_k^*$, $W=[\operatorname{vec}(V_1)\ \cdots\ \operatorname{vec}(V_r)]$, and $\Psi_T(X)=\sum_{k,l}T_{kl}V_kXV_l^*$. An effect $T$ determines the pair $(\Psi_T,\Psi_{I-T})$ with common sum $\Omega$. This parametrizes exactly the source's pairs and derivatives, by the ARN correspondence. All derivatives compared use this same family.
--
--   A Kubo–Ando mean $\sigma$ has a nonnegative operator-monotone representing function $f_\sigma$ with $f_\sigma(1)=1$. Set $g_\sigma(t)=t f_\sigma((1-t)/t)$ for $0<t<1$, $g_\sigma(0)=f_\sigma'(\infty)$, and $g_\sigma(1)=f_\sigma(0+)$. Matrix functions use spectral functional calculus and singular means use decreasing positive regularization.
--
--   For an effect $T$, let $\Phi=\Psi_T$ and $\Psi=\Psi_{I-T}$. Then
--
--   $$J(\Phi)\,\sigma\,J(\Psi)=Wg_\sigma(T)W^* = WT^{1/2}f_\sigma(T^{-1/2}(I-T)T^{-1/2})T^{1/2}W^*.$$
--
--   The last expression is literal when $T$ and $I-T$ are positive definite, and otherwise denotes the decreasing regularization from above. The intrinsic Kraus mean $\Phi\sigma\Psi$ is a CP submap of $\Omega$, equals $\Psi_{g_\sigma(T)}$, and its ARN derivative has spectrum $g_\sigma(\operatorname{spec}T)$. The zero-map case uses an empty Kraus family and empty spectrum. This connects the intrinsic and Choi descriptions without defining either by the asserted identity.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 7, Theorem 2.13

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Theorem 2.13, source PDF pp.7–8. Phi=Psi_T and Psi=Psi_(I-T) eliminate the
derivative binders by the defining ARN relation; the mean itself was defined intrinsically. -/
theorem theorem_2_13 {dx dy r : ℕ}
    (s : Mean) (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (hV : LinearIndependent ℂ V)
    (T : M r) (hT : IsEffect T) :
    connectionOp s.toConnection (choiMatrix (arnFamily V T)) (choiMatrix (arnFamily V (1 - T))) =
      krausColumnMatrix V * cfc (meanPerspective s) T * (krausColumnMatrix V)ᴴ ∧
    Tendsto (fun e : ℝ => krausColumnMatrix V *
      perspective s.f ((1 - T) + (e : ℂ) • 1) (T + (e : ℂ) • 1) * (krausColumnMatrix V)ᴴ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (krausColumnMatrix V * cfc (meanPerspective s) T * (krausColumnMatrix V)ᴴ)) ∧
    (T.PosDef → (1 - T).PosDef →
      krausColumnMatrix V * cfc (meanPerspective s) T * (krausColumnMatrix V)ᴴ =
        krausColumnMatrix V * perspective s.f (1 - T) T * (krausColumnMatrix V)ᴴ) ∧
    cpOrder (cpMean s (arnFamily V T) (arnFamily V (1 - T))) (krausMap V) ∧
    cpMean s (arnFamily V T) (arnFamily V (1 - T)) = arnFamily V (cfc (meanPerspective s) T) ∧
    spectrum ℝ (cfc (meanPerspective s) T) = meanPerspective s '' spectrum ℝ T := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
