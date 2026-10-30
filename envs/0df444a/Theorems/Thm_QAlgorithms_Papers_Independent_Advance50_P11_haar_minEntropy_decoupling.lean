-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_haar_minEntropy_decoupling
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.haar_minEntropy_decoupling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:45:44.61342+00:00
-- url     : https://prove2.me/theorems/e7748dad-84e7-4529-a807-bc7535fa3122
-- title:
--   Haar compression bound in terms of fixed-reference min entropy
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. Here $H_{\min}(\rho_{AB}\mid\sigma_B)$ is the fixed-reference min entropy, and $H_{\max}(\rho_{AB}\mid\sigma_B)$ is the historical support-rank max entropy, $\log_2\operatorname{tr}[(I_A\otimes\sigma_B)\Pi_{\rho_{AB}}]$, where $\Pi_\rho$ is the support projector. A conditioning register in place of a reference density means a supremum over normalized reference densities. Let $\rho_{AR},\sigma_R$ be density operators satisfying $\operatorname{supp}\rho_R\subseteq\operatorname{supp}\sigma_R$. Let $d=\dim A>0$, $L=\dim A_1>0$, $PP^{\dagger}=I_{A_1}$, and $U$ be Haar distributed on $A$. Put $\omega^U=(PU\otimes I_R)\rho_{AR}(PU\otimes I_R)^{\dagger}$, $\rho_R=\operatorname{tr}_A\rho_{AR}$, and $\tau_{A_1}=I/L$. Then
--
--   $$
--   \mathbb E_U\left\|\frac dL\omega^U-\tau_{A_1}\otimes\rho_R\right\|_1
--   \le2^{-\frac12(H_{\min}(\rho_{AR}\mid\sigma_R)-\log_2L)}.
--   $$
--
--   The support condition ensures that the displayed entropy is finite, including singular supported references.
--
--   This is the explicit technical Hmin consequence of the collision bound, not an operational merging theorem.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 20, unnumbered-Hmin-decoupling

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P11

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Support50.P21
  (conditionalMin conditionalMax hMin hMax largestEigenvalue)

open QAlgorithms.Papers.Independent.Dependency50.P35 (elog supportRank tr)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC marginalAR)

open QAlgorithms.Papers.Independent.Information100.P22 (bell mixed)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Unnumbered Hmin consequence, PDF p.20 following (4.22).
The support guard is the one explicitly required by the invoked Lemma 3.20.
As in corrected Lemma 4.5, P is a coisometry; supported normalized inputs make Hmin finite. -/
theorem haar_minEntropy_decoupling {d L : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    [Nonempty R] (hd : 0 < d) (hL : 0 < L)
    (rho : Matrix (Fin d × R) (Fin d × R) ℂ) (sigma : Matrix R R ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportIncluded (traceLeft rho) sigma)
    (P : Matrix (Fin L) (Fin d) ℂ) (hP : P * Pᴴ = 1) :
    (∫ U, traceNorm ((((d : ℝ) / (L : ℝ) : ℝ) : ℂ) • compressedState rho P U -
      Matrix.kronecker (mixed (Fin L)) (traceLeft rho)) ∂(Schur.unitaryHaar d)) ≤
      (2 : ℝ) ^ (-(1 / 2 : ℝ) *
        ((conditionalMin rho sigma).toReal - Real.logb 2 L)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end
