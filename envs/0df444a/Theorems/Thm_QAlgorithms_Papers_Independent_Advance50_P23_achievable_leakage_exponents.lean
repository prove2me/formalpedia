-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_achievable_leakage_exponents
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.achievable_leakage_exponents
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:30:19.550999+00:00
-- url     : https://prove2.me/theorems/c844a6d9-f9ba-45fc-8482-45ce90bfc2c6
-- title:
--   Sections IV.B–C: achievable leakage exponents and their alternative bounds
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   Fix $R\ge0$, any positive message and auxiliary sizes $M_n,L_n$, and laws $P_{L_n}$ with $H_2(P_{L_n})\ge nR$. Let $a_n,b_n$ be the iid-$P_X^{\otimes n}$ table-ensemble mean Holevo and full trace-norm leakages. Define $\underline e(a)=\liminf_n[-\log a_n/n]$ with $-\log0=+\infty$. Then
--   $$\underline e(a)\ge e_R:=\max_{0\le s\le1}s(R-I_s(W_E,P_X)),\qquad
--   \underline e(b)\ge e_G:=\max_{0\le s\le1}\frac s2(R-I_s^G(W_E,P_X)).$$
--   Both maxima are attained and their zero-parameter objectives equal zero. These are lower-asymptotic secrecy statements; no ordinary exponent limit or reliability follows from the entropy condition alone.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
--
--   Section IV.C further gives $e_I\ge e_G$ and $e_d\ge e_R/2$ for these same ensemble sequences, where $e_I$ and $e_d$ mean the extended lower asymptotic exponents defined above.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 13, Sections IV.B–C: achievable leakage exponents and their alternative bounds

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

/-- PDF pp.13–14, Sections IV.B–C: liminf bounds, not unproved ordinary exponent
limits. Section IV.C also bounds the information-leakage exponent by eG and the
trace-leakage exponent by eR/2. Only secrecy is asserted from H2(PL_n)>=nR; no
reliability conclusion is inferred without its separate codebook-rate condition.
Both closed-interval maxima are attained. Printed ordinary limits are changed to
extended liminf because the allowed size/law sequences need not have convergent
decay rates; zero leakage has exponent +infinity. -/
theorem achievable_leakage_exponents [Nonempty X] [Nonempty E]
    (WE : X → Matrix E E ℂ) (hE : hayashiIsCQ WE) (PX : X → ℝ) (hPX : IsLaw PX)
    (M L : ℕ → ℕ) (hM : ∀ n, 0 < M n) (hL : ∀ n, 0 < L n)
    (PL : (n : ℕ) → Fin (L n) → ℝ) (hPL : ∀ n, IsLaw (PL n))
    (R : ℝ) (hR : 0 ≤ R) (hentropy : ∀ n, n * R ≤ hayashiRenyiEntropy 1 (PL n)) :
    (exponentR R WE PX : EReal) ≤ lowerExponent (fun n => ensembleInfo (M n) (L n)
      (productOutput n WE) (hayashiProductLaw n PX) (PL n)) ∧
    (exponentG R WE PX : EReal) ≤ lowerExponent (fun n => ensembleTrace (M n) (L n)
      (productOutput n WE) (hayashiProductLaw n PX) (PL n)) ∧
    (exponentG R WE PX : EReal) ≤ lowerExponent (fun n => ensembleInfo (M n) (L n)
      (productOutput n WE) (hayashiProductLaw n PX) (PL n)) ∧
    ((exponentR R WE PX / 2 : ℝ) : EReal) ≤ lowerExponent (fun n => ensembleTrace (M n) (L n)
      (productOutput n WE) (hayashiProductLaw n PX) (PL n)) ∧
    (∃ s ∈ Set.Icc (0 : ℝ) 1, exponentR R WE PX = s * (R - petzInfo s WE PX)) ∧
    (∃ s ∈ Set.Icc (0 : ℝ) 1, exponentG R WE PX = s / 2 * (R - gallagerInfo s WE PX)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
