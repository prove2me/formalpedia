-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_gallager_convex_concave
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.gallager_convex_concave
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:21:39.710946+00:00
-- url     : https://prove2.me/theorems/d91ff8de-77f1-45c6-9720-129758cff219
-- title:
--   Lemma 3: convexity/concavity of the Gallager trace functional
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   On the full probability simplex define $F_s(P)=\operatorname{Tr}(\sum_xP(x)W_x^{1+s})^{1/(1+s)}$. Then
--   $$F_s\text{ is convex for }-\tfrac12\le s\le0,\qquad F_s\text{ is concave for every finite }s\ge0.$$
--   The concrete trace gives a defined value at zero without multiplying an undefined information quantity by zero.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 5, Lemma 3: convexity/concavity of the Gallager trace functional

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

/-- PDF p.5, Lemma 3: convexity on [-1/2,0] and concavity for every finite s>=0,
on the probability simplex. The concrete trace avoids zero times undefined information. -/
theorem gallager_convex_concave [Nonempty X] [Nonempty E]
    (W : X → Matrix E E ℂ) (hW : hayashiIsCQ W) :
    (∀ s ∈ Set.Icc (-(1 / 2 : ℝ)) 0,
      ConvexOn ℝ {P : X → ℝ | IsLaw P} (gallagerTrace s W)) ∧
    (∀ s : ℝ, 0 ≤ s → ConcaveOn ℝ {P : X → ℝ | IsLaw P} (gallagerTrace s W)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
