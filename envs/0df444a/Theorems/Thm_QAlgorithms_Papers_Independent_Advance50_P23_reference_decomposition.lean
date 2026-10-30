-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_reference_decomposition
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.reference_decomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:45:34.694347+00:00
-- url     : https://prove2.me/theorems/7adbdf53-ff18-4884-af65-84efbc0e212d
-- title:
--   Unnumbered (30)–(31): reference state decomposition and minimizer
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   For every normalized cq ensemble $(W,P)$ and every reference density matrix $\sigma$, the extended reference information satisfies
--   $$I(W,P\Vert\sigma)=I(W,P)+D(\bar W_P\Vert\sigma)\ge I(W,P),$$
--   $$I(W,P\Vert\bar W_P)=I(W,P).$$
--   Here $D$ is Umegaki relative entropy, taking $+\infty$ when support inclusion fails. The additive form avoids subtracting infinities and states attainment of the minimum at the actual average state.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 4, Unnumbered (30)–(31): reference state decomposition and minimizer

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

/-- PDF p.4, (30)–(31): extended-additive reference decomposition and attained
minimum. Unlike subtracting two infinite quantities, this has no infinity-minus-infinity. -/
theorem reference_decomposition [Nonempty X] [Nonempty E]
    (W : X → Matrix E E ℂ) (hW : hayashiIsCQ W) (P : X → ℝ) (hP : IsLaw P) :
    (∀ sigma : Matrix E E ℂ, IsDensityMatrix sigma →
      referenceInfo 0 W P sigma = (holevo P W : EReal) + relativeEntropy (average W P) sigma ∧
      (holevo P W : EReal) ≤ referenceInfo 0 W P sigma) ∧
    referenceInfo 0 W P (average W P) = (holevo P W : EReal) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
