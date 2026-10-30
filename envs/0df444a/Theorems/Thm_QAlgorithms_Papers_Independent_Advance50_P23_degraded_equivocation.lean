-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_degraded_equivocation
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.degraded_equivocation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:34:44.581434+00:00
-- url     : https://prove2.me/theorems/8bec34f1-f92c-4d0b-bd48-382891fac2f4
-- title:
--   Lemma 8, (105): degraded equivocation single-letterization
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   Suppose a finite-dimensional CPTP map $\mathcal D$ satisfies $\mathcal D(W_{B,x})=W_{E,x}$ for every input. For a feasible communication rate $0\le R\le C_B$, let $H(R)$ be the constrained regularized private-information function of (100). Then
--   $$H(R)=\max_{P:\ I(W_B,P)\ge R}\{I(W_B,P)-I(W_E,P)\}.$$
--   The maximum is attained by a normalized input law. Degradation is represented by an actual normalized Kraus channel, and concavity is not supplied as a hypothesis.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 17, Lemma 8, (105): degraded equivocation single-letterization

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

/-- PDF pp.17–18, Lemma 8, (105): an ACTUAL CPTP degrading map implies the
constrained single-letter formula, with an attained feasible maximum. Concavity
of private information is theorem content, not an assumed substitute for degradation. -/
theorem degraded_equivocation {X B E : Type} [Fintype X] [Fintype B] [Fintype E]
    [Nonempty X] [Nonempty B] [Nonempty E] [DecidableEq B] [DecidableEq E]
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ) (hB : hayashiIsCQ WB) (hE : hayashiIsCQ WE)
    (D : Superop B E) (hD : IsChannel D) (hdegraded : ∀ x, D (WB x) = WE x)
    (R : ℝ) (hR : 0 ≤ R) (hfeasible : R ≤ receiverCapacity WB) :
    ∃ P : X → ℝ, IsLaw P ∧ R ≤ holevo P WB ∧
      equivocationFunction R WB WE = (holevo P WB - holevo P WE : ℝ) ∧
      ∀ Q : X → ℝ, IsLaw Q → R ≤ holevo Q WB →
        holevo Q WB - holevo Q WE ≤ holevo P WB - holevo P WE := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
