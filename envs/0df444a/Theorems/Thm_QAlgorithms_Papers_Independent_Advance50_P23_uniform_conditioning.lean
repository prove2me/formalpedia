-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_uniform_conditioning
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.uniform_conditioning
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:43:08.255772+00:00
-- url     : https://prove2.me/theorems/96cda11d-9bee-45ee-a7ba-496597940190
-- title:
--   Unnumbered (47), Appendix B: factor-two conditioning inequality
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   Let $W_{x,y}$ be normalized density matrices indexed by independent uniform $X,Y$. Put $\bar W_y=|X|^{-1}\sum_xW_{x,y}$ and $\bar W=(|X||Y|)^{-1}\sum_{x,y}W_{x,y}$. Then
--   $$\frac1{|X||Y|}\sum_{x,y}\|W_{x,y}-\bar W_y\|_1\le\frac2{|X||Y|}\sum_{x,y}\|W_{x,y}-\bar W\|_1.$$
--   This is exactly $d'_1(X;Y,E)\le2d'_1(X,Y;E)$ under independent uniform classical laws; it is not a statement about arbitrary correlated classical inputs.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 6, Unnumbered (47), Appendix B: factor-two conditioning inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P23

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

open QAlgorithms.Papers.Independent.Information100.P56
  (IsLaw entropy average holevo uniform ProjectiveRep orbit productOutput)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch logNonnegativeExtended)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X A Z B E : Type} [Fintype X] [Fintype A] [Fintype Z]
  [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- PDF pp.6,29, (47): conditioning on an independent uniform classical register
costs at most two in FULL trace norm. The conditional and joint quantities are
written as their explicit cq block sums. -/
theorem uniform_conditioning [Nonempty X] [Nonempty A] [Nonempty E]
    (W : X × A → Matrix E E ℂ) (hW : hayashiIsCQ W) :
    (∑ x, ∑ a, (Fintype.card X : ℝ)⁻¹ * (Fintype.card A : ℝ)⁻¹ *
      traceNorm (W (x,a) - ∑ y : X, ((Fintype.card X : ℝ)⁻¹ : ℂ) • W (y,a))) ≤
    2 * traceCorrelation (uniform : X × A → ℝ) W := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
