-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_exponent_comparison
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.exponent_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:31:29.275989+00:00
-- url     : https://prove2.me/theorems/8f9a7efa-b6f1-4ebf-bc98-60d5151ebf54
-- title:
--   Lemma 7, (88)–(89): comparison of leakage exponents
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   For the sacrifice-information rate $R\ge0$, let $e_R=\max_{0\le s\le1}s(R-I_s)$ and $e_G=\max_{0\le s\le1}s(R-I_s^G)/2$, evaluated at the same normalized cq ensemble. Then
--   $$\tfrac12e_R\le e_G.$$
--   If every pair of channel outputs commutes, also
--   $$e_G\le e_R.$$
--   The commuting hypothesis is required only for the second conclusion; both optimizations include their continuous zero value.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 14, Lemma 7, (88)–(89): comparison of leakage exponents

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

/-- PDF pp.14–15, Lemma 7, (88)–(89): only the second comparison assumes commuting
outputs. R is the nonnegative sacrifice-information rate, not the message rate. -/
theorem exponent_comparison [Nonempty X] [Nonempty E]
    (W : X → Matrix E E ℂ) (hW : hayashiIsCQ W) (P : X → ℝ) (hP : IsLaw P)
    (R : ℝ) (hR : 0 ≤ R) :
    exponentR R W P / 2 ≤ exponentG R W P ∧
    ((∀ x y, W x * W y = W y * W x) → exponentG R W P ≤ exponentR R W P) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
