-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_haar_collision_decoupling
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.haar_collision_decoupling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:33:45.253989+00:00
-- url     : https://prove2.me/theorems/4b490478-1d9a-4614-95d9-8bc854d1bfad
-- title:
--   Haar compression bound with the required support guard
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. Let $\rho_{AR}$ and $\sigma_R$ be density operators with $\operatorname{supp}\rho_R\subseteq\operatorname{supp}\sigma_R$, where $\rho_R=\operatorname{tr}_A\rho_{AR}$. Let $d=\dim A>0$, $L=\dim A_1>0$, and let $P:A\to A_1$ satisfy $PP^{\dagger}=I_{A_1}$. For a Haar-distributed unitary $U$ on $A$, put $\omega^U=(PU\otimes I_R)\rho_{AR}(PU\otimes I_R)^{\dagger}$ and $\tau_{A_1}=I/L$. Using the collision entropy defined by generalized inverse quarter powers,
--
--   $$
--   \mathbb E_U\left\|\frac dL\omega^U-\tau_{A_1}\otimes\rho_R\right\|_1
--   \le 2^{-\frac12(H_2(\rho_{AR}\mid\sigma_R)-\log_2L)}.
--   $$
--
--   The Haar law is normalized on the entire unitary group. The support guard makes $H_2$ finite; $d=L=1$ is included.
--
--   This is the corrected technical compression estimate, with the proof-required support domain made explicit.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 19, Lemma 4.5

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

/-- Lemma 4.5, PDF pp.19--20, (4.13), with the proof-required support correction.
PRINTED: arbitrary normalized sigma_R. CHANGED: supp(rho_R) subset supp(sigma_R).
WHY: the invocation of A.6 needs this; inverse-on-support otherwise erases a nonzero part.
P is a coisometry onto the L-dimensional subspace. d=L=1 is included.
The support guard ensures collisionEntropy is finite, so toReal never uses an infinity fallback. -/
theorem haar_collision_decoupling {d L : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    [Nonempty R] (hd : 0 < d) (hL : 0 < L)
    (rho : Matrix (Fin d × R) (Fin d × R) ℂ) (sigma : Matrix R R ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportIncluded (traceLeft rho) sigma)
    (P : Matrix (Fin L) (Fin d) ℂ) (hP : P * Pᴴ = 1) :
    (∫ U, traceNorm ((((d : ℝ) / (L : ℝ) : ℝ) : ℂ) • compressedState rho P U -
      Matrix.kronecker (mixed (Fin L)) (traceLeft rho)) ∂(Schur.unitaryHaar d)) ≤
      (2 : ℝ) ^ (-(1 / 2 : ℝ) *
        ((collisionEntropy rho sigma).toReal - Real.logb 2 L)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end
