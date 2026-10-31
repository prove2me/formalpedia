-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P04_keyImperfections
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P04.keyImperfections
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:50:07.14274+00:00
-- url     : https://prove2.me/theorems/37c915a3-2221-4c17-9d92-c6ece62f64eb
-- title:
--   Near-pure Z ancilla implies privacy and approximate uniformity
-- statement:
--   There is an absolute integer $r_0$ such that the following holds for $r\ge\max\{r_0,1\}$ and $0\le\eta\le1/2$. Let $\rho_Q$ be the reduced density operator of an $r$-qubit factor of any positive trace-class joint state, with arbitrary quantum and public side information held by Eve. Assume $\langle0|\rho_Q|0\rangle_Z\ge1-\eta$. Let $p_y$ be the complete X-measurement distribution, $H(p)$ its Shannon entropy in bits, $S$ von Neumann entropy in bits, and $I_{\rm acc}$ the supremum of the mutual information over Eve's measurements. Then $p$ is a probability distribution and
--
--   $$
--   I_{\rm acc}\le S(\rho_Q)\le h(\eta)+\eta\log_2(2^r-1),\qquad
--   2^{-r}\left(\sum_y\sqrt{p_y}\right)^2\ge1-\eta,
--   $$
--
--   $$
--   H(p)\ge r(2\sqrt{1-\eta}-1)\ge r(1-2\eta).
--   $$
--
--   For $\eta>0$, also $S(\rho_Q)<h(\eta)+r\eta$. At $\eta=0$, $I_{\rm acc}=0$ and $p_y=2^{-r}$ for every $y$. Here $h(t)=-t\log_2t-(1-t)\log_2(1-t)$, with $0\log 0=0$.
--
--   These conditional state-to-key estimates quantify both imperfections; they do not replace the full protocol's acceptance-conditioned security result.
-- source:
--   Secure quantum key distribution with an uncharacterized source, arXiv:quant-ph/0208155v2, PDF p. 4, Conclusions (a),(b) after Eq.(12)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P04

noncomputable section

universe u v w

namespace QAlgorithms.Papers.Independent.Intakenext100.P04

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P13
  (State IsTraceClass IsPositive operatorTrace)

open QAlgorithms.Papers.Independent.Advance50.P18 (keyEntropy)

open scoped ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Koashi–Preskill PDF p.4(a),(b), following Eq.(12). The threshold is absolute,
before eta, the state and Eve's Hilbert space. The strict entropy bound excludes
eta=0, where exact uniformity and zero information are asserted instead.
This is a state-to-key estimate, not the deferred accepted-protocol theorem. -/
theorem keyImperfections :
    ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → 1 ≤ r → ∀ eta : ℝ,
      0 ≤ eta → eta ≤ 1 / 2 →
      ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        {I : Type v} (b : HilbertBasis I ℂ H) (rho : State b) (A : QubitFactor r H),
      1 - eta ≤ (qubitMarginal b rho A 0 0).re →
      let sigma := qubitMarginal b rho A
      let p := keyLaw b rho A
      IsDensityMatrix sigma ∧
      (∀ y, 0 ≤ p y) ∧ (∑ y, p y) = 1 ∧
      accessibleKeyInfo b rho A ≤ vnEntropy sigma ∧
      vnEntropy sigma ≤ binEntropy2 eta + eta * Real.logb 2 ((2 : ℝ) ^ r - 1) ∧
      (0 < eta → vnEntropy sigma < binEntropy2 eta + r * eta) ∧
      1 - eta ≤ uniformKeyFidelity p ∧
      (r : ℝ) * (2 * Real.sqrt (1 - eta) - 1) ≤ keyEntropy p ∧
      (r : ℝ) * (1 - 2 * eta) ≤ (r : ℝ) * (2 * Real.sqrt (1 - eta) - 1) ∧
      (eta = 0 → accessibleKeyInfo b rho A = 0 ∧
        ∀ y, p y = ((2 : ℝ) ^ r)⁻¹) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P04

end
