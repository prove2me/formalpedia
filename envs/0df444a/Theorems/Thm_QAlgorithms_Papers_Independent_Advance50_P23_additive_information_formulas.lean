-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_additive_information_formulas
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.additive_information_formulas
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:38:00.080835+00:00
-- url     : https://prove2.me/theorems/469df704-5aff-4be1-841f-1d7d8104cb62
-- title:
--   Unnumbered (126)–(128): additive pure-state information formulas
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   Let $W_x=U_x\rho U_x^\dagger$ be the orbit of a density matrix under a projective representation of a finite additive module, and put $\bar\rho=|X|^{-1}\sum_xW_x$. For $0\le s\le1$,
--   $$sI_s(W,\rm unif)=\log\operatorname{Tr}\rho^{1+s}\bar\rho^{-s},\quad I(W,\rm unif)=H(\bar\rho)-H(\rho),$$
--   $$\frac{s}{1+s}I_s^G(W,\rm unif)=\log\operatorname{Tr}\left(|X|^{-1}\sum_xU_x\rho^{1+s}U_x^\dagger\right)^{1/(1+s)}.$$
--   If $\rho$ is pure, additionally
--   $$sI_s=\log\operatorname{Tr}\bar\rho^{1-s},\quad I=H(\bar\rho),\quad\frac{s}{1+s}I_s^G=\log\operatorname{Tr}\bar\rho^{1/(1+s)}.$$
--   Here $H$ is natural von Neumann entropy. At $s=1$, the zeroth power is the support projection, not the identity on an unused kernel.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 22, Unnumbered (126)–(128): additive pure-state information formulas

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

/-- PDF pp.21–22, (126)–(128), including the general orbit formulas preceding
(126). At s=1 the zero power is the support projection of the average output. -/
theorem additive_information_formulas {K G : Type} [Ring K] [AddCommGroup G] [Module K G]
    [Fintype G] [Nonempty E] (U : ProjectiveRep (Multiplicative G) E)
    (rho : Matrix E E ℂ) (hrho : IsDensityMatrix rho)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    let W := fun x : G => orbit U rho (Multiplicative.ofAdd x)
    let bar := average W (uniform : G → ℝ)
    s * petzInfo s W uniform = Real.log ((supportPower rho (1 + s) * supportPower bar (-s)).trace.re) ∧
    holevo uniform W = entropy bar - entropy rho ∧
    s / (1 + s) * gallagerInfo s W uniform = Real.log (gallagerTrace s W uniform) ∧
    (rho * rho = rho →
      s * petzInfo s W uniform = Real.log ((supportPower bar (1 - s)).trace.re) ∧
      holevo uniform W = entropy bar ∧
      s / (1 + s) * gallagerInfo s W uniform = Real.log ((supportPower bar (1 / (1 + s))).trace.re)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
