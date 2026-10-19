-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_proposition_A_1
-- name    : QAlgorithms.Papers.Independent.Information100.P50.proposition_A_1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:10:52.828637+00:00
-- url     : https://prove2.me/theorems/cebe674f-1ee6-4858-a379-da367f3bd779
-- title:
--   Proposition A.1: For every Kubo–Ando mean sigma and p∈[1,infinity], norm_(p→p)(Phi sigma Psi)≤specNorm(g_sigma(T))*norm_(p→p)(O
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For a fixed linearly independent Kraus family $(V_k)_{k=1}^r$, put $\Omega(X)=\sum_k V_kXV_k^*$, $W=[\operatorname{vec}(V_1)\ \cdots\ \operatorname{vec}(V_r)]$, and $\Psi_T(X)=\sum_{k,l}T_{kl}V_kXV_l^*$. An effect $T$ determines the pair $(\Psi_T,\Psi_{I-T})$ with common sum $\Omega$. This parametrizes exactly the source's pairs and derivatives, by the ARN correspondence. All derivatives compared use this same family.
--
--   A Kubo–Ando mean $\sigma$ has a nonnegative operator-monotone representing function $f_\sigma$ with $f_\sigma(1)=1$. Set $g_\sigma(t)=t f_\sigma((1-t)/t)$ for $0<t<1$, $g_\sigma(0)=f_\sigma'(\infty)$, and $g_\sigma(1)=f_\sigma(0+)$. Matrix functions use spectral functional calculus and singular means use decreasing positive regularization.
--
--   For every Schatten exponent $p\in[1,\infty]$ and effect $T$,
--
--   $$\|\Psi_T\sigma\Psi_{I-T}\|_{p\to p}\le\|g_\sigma(T)\|_\infty\|\Omega\|_{p\to p}.$$
--
--   When $r>0$,
--
--   $$\|g_\sigma(T)\|_\infty=\max_{t\in\operatorname{spec}T}g_\sigma(t).$$
--
--   At $p=1$, the induced and completely bounded trace norms agree and equal the attained maximum
--
--   $$\max_{\rho\in\mathcal D(X)}\operatorname{tr}(g_\sigma(T)^\top\Omega^c(\rho)).$$
--
--   Here $\Omega^c$ is the complementary CP map in this Kraus representation and $\mathcal D(X)$ is the set of PSD trace-one inputs. At $r=0$ the mean and both displayed operator/trace norms are zero, without an empty spectral maximum. This gives the all-Schatten norm estimate and its exact trace specialization.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 26, Proposition A.1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Proposition A.1, source PDF p.26. All p in [1,infinity], including infinity.
Spectral and density-state maxima are attained; the empty spectral case is separate. -/
theorem proposition_A_1 {dx dy r : ℕ} (hdx : 0 < dx) (hdy : 0 < dy)
    (s : Mean) (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (hV : LinearIndependent ℂ V)
    (T : M r) (hT : IsEffect T) :
    (∀ p : ℝ≥0∞, 1 ≤ p →
      inducedNorm p (cpMean s (arnFamily V T) (arnFamily V (1 - T))) ≤
        specNorm (cfc (meanPerspective s) T) * inducedNorm p (krausMap V)) ∧
    (0 < r → IsGreatest (meanPerspective s '' spectrum ℝ T) (specNorm (cfc (meanPerspective s) T))) ∧
    inducedNorm 1 (cpMean s (arnFamily V T) (arnFamily V (1 - T))) =
      cbTraceNorm (cpMean s (arnFamily V T) (arnFamily V (1 - T))) ∧
    (∃ rho : M dx, IsDensityMatrix rho ∧
      cbTraceNorm (cpMean s (arnFamily V T) (arnFamily V (1 - T))) =
        ((cfc (meanPerspective s) T).transpose * complementaryMap V rho).trace.re ∧
      ∀ tau : M dx, IsDensityMatrix tau →
        ((cfc (meanPerspective s) T).transpose * complementaryMap V tau).trace.re ≤
          ((cfc (meanPerspective s) T).transpose * complementaryMap V rho).trace.re) ∧
    (r = 0 → cpMean s (arnFamily V T) (arnFamily V (1 - T)) = 0 ∧
      specNorm (cfc (meanPerspective s) T) = 0 ∧
      cbTraceNorm (cpMean s (arnFamily V T) (arnFamily V (1 - T))) = 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
