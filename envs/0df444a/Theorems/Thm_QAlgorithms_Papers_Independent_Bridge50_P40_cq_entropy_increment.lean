-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P40_cq_entropy_increment
-- name    : QAlgorithms.Papers.Independent.Bridge50.P40.cq_entropy_increment
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:03:19.431408+00:00
-- url     : https://prove2.me/theorems/0242c263-d866-4c0e-b306-64d533029c10
-- title:
--   Two-sided cq Rényi entropy increment bound
-- statement:
--   All registers are finite and nonempty. Density operators have trace one, pure states are normalized, all entropies and logarithms are in base two, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Write $S_a$ for Petz Rényi entropy, with support projection at order zero and the von Neumann limit at order one; $S_\infty(\rho)=-\log_2\lambda_{\max}(\rho)$.
--
--   Let $\omega^{RX}=\sum_xp_x\rho_x^R\otimes|x\rangle\langle x|$, where $X$ is finite nonempty, $p$ is a probability vector and each $\rho_x$ is a density operator. Zero-weight letters are allowed, and $\omega^R=\operatorname{Tr}_X\omega$. For $a\in[0,2]\setminus\{1\}$,
--
--   $$
--   0\le S_a(RX)_\omega-S_a(R)_\omega\le\log_2|X|.
--   $$
--
--   Both sides and the printed order domain are retained. At order zero the entropies use the actual support ranks, not ambient dimensions.
-- source:
--   A strong converse for the quantum state merging protocol, arXiv:1404.5940v1, PDF p. 13, Lemma 15, equation (72)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P40

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply marginalAR)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (cq)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.13--14, Lemma 15, (72): both sides, including order zero and
excluding order one exactly as printed. The marginal comes from the same cq state. -/
theorem cq_entropy_increment {R X : Type} [Fintype R] [Fintype X]
    [Nonempty R] [Nonempty X]
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (rho : X → Matrix R R ℂ) (hrho : ∀ x, IsDensityMatrix (rho x))
    (a : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) (ha1 : a ≠ 1) :
    0 ≤ renyiEntropy a (cq p rho) - renyiEntropy a (traceRight (cq p rho)) ∧
    renyiEntropy a (cq p rho) - renyiEntropy a (traceRight (cq p rho)) ≤
      Real.logb 2 (Fintype.card X) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P40

end
