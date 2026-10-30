-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_pinsker_ensemble_alternative
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.pinsker_ensemble_alternative
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:28:43.763994+00:00
-- url     : https://prove2.me/theorems/1803c00a-017f-4b2b-87b2-2c6a3c89be22
-- title:
--   Unnumbered (80): Pinsker-based trace-norm alternative
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   For a message-output cq channel $V$, $I_{\rm mix}(V)$ and $d_{1,\rm mix}(V)$ are its uniform-message Holevo information and full trace-norm correlation. Their maximum versions optimize over every message law. A code has an actual stochastic encoder and a normalized message POVM; $\epsilon$ and $\epsilon_{\max}$ denote its average and worst-message error. “Uses $P_L$” means each encoder row is a pushforward of that sole auxiliary law under a deterministic table chosen before communication.
--
--   For the same iid table ensemble and $0<s\le1$, let $D_c=d_{1,\rm mix}(W_E\circ\Gamma[c])$. Then
--   $$\mathbb E_cD_c\le\sqrt{\mathbb E_cD_c^2}\le\sqrt{\frac{2v^s}{s}}\,e^{\frac s2(I_s(W_E,P_X)-H_{1+s}(P_L))}.$$
--   This keeps both inequalities in (80) and the full trace-norm normalization.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 12, Unnumbered (80): Pinsker-based trace-norm alternative

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

/-- PDF p.12, (80): the first-moment / second-moment chain and Pinsker alternative,
with the full trace norm and the factor sqrt(2 v^s/s). -/
theorem pinsker_ensemble_alternative [Nonempty X] [Nonempty E]
    (WE : X → Matrix E E ℂ) (hE : hayashiIsCQ WE)
    (M L : ℕ) (hM : 0 < M) (hL : 0 < L)
    (PX : X → ℝ) (hPX : IsLaw PX) (PL : Fin L → ℝ) (hPL : IsLaw PL)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    let D := fun c : Fin L → Fin M → X => traceCorrelation uniform (hayashiCompose WE (tableEncoder PL c))
    (∑ c, bookLaw PX c * D c) ≤ Real.sqrt (∑ c, bookLaw PX c * (D c)^2) ∧
    Real.sqrt (∑ c, bookLaw PX c * (D c)^2) ≤
      Real.sqrt (2 * Real.rpow (eigenCount (average WE PX)) s / s) *
        Real.exp (s / 2 * (petzInfo s WE PX - hayashiRenyiEntropy s PL)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
