-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_renyi_radius
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.renyi_radius
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:20:36.126909+00:00
-- url     : https://prove2.me/theorems/3f486478-5179-4bcf-b55f-3b97d6c4987a
-- title:
--   Lemma 1, (34)–(35): attained Renyi information radius
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   For any real $s>-1$, let $\sigma_s=A_s^{1/(1+s)}/\operatorname{Tr}A_s^{1/(1+s)}$. With $I_s(W,P\Vert\sigma)$ denoting the information relative to reference state $\sigma$, the reference is a density matrix and
--   $$I_s(W,P\Vert\sigma_s)=I_s^G(W,P)\le I_s(W,P\Vert\sigma)\quad\text{for every density matrix }\sigma,$$
--   $$I_s^G(W,P)\le I_s(W,P).$$
--   This states an attained minimum, including the Umegaki/Holevo case $s=0$. Reference information is extended real, with positive-order support failure giving $+\infty$.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 5, Lemma 1, (34)–(35): attained Renyi information radius

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

/-- PDF p.5, Lemma 1, (34)–(35): the explicit reference attains the normalized-state
minimum for every finite s>-1, including the Umegaki limit at zero. -/
theorem renyi_radius [Nonempty X] [Nonempty E]
    (W : X → Matrix E E ℂ) (hW : hayashiIsCQ W) (P : X → ℝ) (hP : IsLaw P)
    (s : ℝ) (hs : -1 < s) :
    IsDensityMatrix (renyiOptimizer s W P) ∧
    referenceInfo s W P (renyiOptimizer s W P) = (gallagerInfo s W P : EReal) ∧
    (∀ sigma : Matrix E E ℂ, IsDensityMatrix sigma →
      (gallagerInfo s W P : EReal) ≤ referenceInfo s W P sigma) ∧
    gallagerInfo s W P ≤ petzInfo s W P := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
