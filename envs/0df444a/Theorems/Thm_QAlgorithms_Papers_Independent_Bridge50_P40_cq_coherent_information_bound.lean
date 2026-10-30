-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P40_cq_coherent_information_bound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P40.cq_coherent_information_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:02:36.478181+00:00
-- url     : https://prove2.me/theorems/921e875f-b766-4054-8e3e-8d1562b08ccc
-- title:
--   Classical-alphabet bound for Rényi coherent information
-- statement:
--   All registers are finite and nonempty. Density operators have trace one, pure states are normalized, all entropies and logarithms are in base two, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Write $S_a$ for Petz Rényi entropy, with support projection at order zero and the von Neumann limit at order one; $S_\infty(\rho)=-\log_2\lambda_{\max}(\rho)$.
--
--   Let $X$ be a finite nonempty alphabet, $p_x\ge0$ with $\sum_xp_x=1$, and $\rho_x^R$ density operators. Put $\omega^{RX}=\sum_xp_x\rho_x^R\otimes|x\rangle\langle x|$, with computed marginal $\omega^R$. For every $a>1$, define
--
--   $$
--   S_a(R|X)_\omega=-\frac{a}{a-1}\log_2\operatorname{Tr}\left[\operatorname{Tr}_R(\omega^{RX})^a\right]^{1/a}.
--   $$
--
--   Then
--
--   $$
--   S_a(R)_\omega-S_a(R|X)_\omega\le\log_2|X|.
--   $$
--
--   This conditional entropy is minus the paper's $I_a(X\rangle R)$; its partial trace retains $X$. No upper bound of two on $a$ is imposed.
-- source:
--   A strong converse for the quantum state merging protocol, arXiv:1404.5940v1, PDF p. 13, Lemma 14, equation (65)

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

/-- PDF p.13, Lemma 14, (65): alphabet bound for the specified coherent-
information conditional entropy. Every a>1 is included; there is no cap at two. -/
theorem cq_coherent_information_bound {R X : Type} [Fintype R] [Fintype X]
    [Nonempty R] [Nonempty X]
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (rho : X → Matrix R R ℂ) (hrho : ∀ x, IsDensityMatrix (rho x))
    (a : ℝ) (ha : 1 < a) :
    renyiEntropy a (traceRight (cq p rho)) - cqCoherentConditional a (cq p rho) ≤
      Real.logb 2 (Fintype.card X) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P40

end
