-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_simultaneous_oneShot
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.simultaneous_oneShot
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:19:36.830992+00:00
-- url     : https://prove2.me/theorems/dff88cf4-7bd5-4c8c-a986-cace1230a8b2
-- title:
--   Theorem 1, (69)–(71): simultaneous one-shot non-uniform wiretap code
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   For a message-output cq channel $V$, $I_{\rm mix}(V)$ and $d_{1,\rm mix}(V)$ are its uniform-message Holevo information and full trace-norm correlation. Their maximum versions optimize over every message law. A code has an actual stochastic encoder and a normalized message POVM; $\epsilon$ and $\epsilon_{\max}$ denote its average and worst-message error. “Uses $P_L$” means each encoder row is a pushforward of that sole auxiliary law under a deterministic table chosen before communication.
--
--   Let $W_B,W_E$ have the same input alphabet, let $M,L\ge1$, and fix laws $P_X,P_L$ on the input and an $L$-point auxiliary alphabet. One $M$-message code using $P_L$ satisfies simultaneously
--   $$\begin{aligned}
--   \epsilon&\le12\inf_{0\le t\le1}(ML)^t e^{-tI_{-t}(W_B,P_X)},\\
--   I_{\rm mix}&\le3\inf_{0<s\le1}\frac{v^s}{s}e^{-sH_{1+s}(P_L)+sI_s(W_E,P_X)},\\
--   d_{1,\rm mix}&\le3\inf_{0<s\le1}\mu_s e^{\frac{s}{2}(I_s^G(W_E,P_X)-H_{1+s}(P_L))}.
--   \end{aligned}$$
--   The reliability objective at $t=0$ is one. The singular secrecy objective at zero is understood by its one-sided extended limit. The same code satisfies every parameter bound.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 10, Theorem 1, (69)–(71): simultaneous one-shot non-uniform wiretap code

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

/-- PDF p.10, Theorem 1, (69)–(71): one common code achieves all three optimized
bounds. Pointwise bounds for every allowed parameter express the displayed infima;
s=0 in the 1/s branch means a one-sided limit, never division by zero. -/
theorem simultaneous_oneShot [Nonempty X] [Nonempty B] [Nonempty E]
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ)
    (hB : hayashiIsCQ WB) (hE : hayashiIsCQ WE) (M L : ℕ) (hM : 0 < M) (hL : 0 < L)
    (PX : X → ℝ) (hPX : IsLaw PX) (PL : Fin L → ℝ) (hPL : IsLaw PL) :
    ∃ C : WiretapCode X B M, UsesLaw PL C ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, hayashiCodeError WB C ≤ 12 * hayashiReliability M L t WB PX) ∧
      (∀ s ∈ Set.Ioc (0 : ℝ) 1, Imix (hayashiCompose WE C.encoder) ≤ 3 * secrecy s WE PX PL) ∧
      (∀ s ∈ Set.Ioc (0 : ℝ) 1, d1mix (hayashiCompose WE C.encoder) ≤ 3 * traceBound s WE PX PL) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
