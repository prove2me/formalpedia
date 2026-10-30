-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_oneShot_equivocation
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.oneShot_equivocation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:32:11.542237+00:00
-- url     : https://prove2.me/theorems/a8d20042-09a6-465a-8dea-b9a6607edb3b
-- title:
--   Theorem 2, (94)–(95): one-shot equivocation bound
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   For a message-output cq channel $V$, $I_{\rm mix}(V)$ and $d_{1,\rm mix}(V)$ are its uniform-message Holevo information and full trace-norm correlation. Their maximum versions optimize over every message law. A code has an actual stochastic encoder and a normalized message POVM; $\epsilon$ and $\epsilon_{\max}$ denote its average and worst-message error. “Uses $P_L$” means each encoder row is a pushforward of that sole auxiliary law under a deterministic table chosen before communication.
--
--   Fix positive $M,L$, laws $P_X,P_L$, the two cq channels, and a secrecy parameter $0<s\le1$. There exists an $M$-message code using only $P_L$ such that
--   $$\epsilon\le8\inf_{0\le t\le1}(ML)^te^{-tI_{-t}(W_B,P_X)},$$
--   $$I_{\rm mix}\le\log v+\frac{\log4+[sI_s(W_E,P_X)-sH_{1+s}(P_L)]_+}{s},\qquad[z]_+=\max\{z,0\}.$$
--   The code may depend on $s$; the independent reliability parameter $t$ is optimized for that same code.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 16, Theorem 2, (94)–(95): one-shot equivocation bound

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

/-- PDF p.16, Theorem 2, (94)–(95): the code is selected AFTER fixing s.
The independent hayashiReliability parameter t is optimized for this same code. -/
theorem oneShot_equivocation [Nonempty X] [Nonempty B] [Nonempty E]
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ)
    (hB : hayashiIsCQ WB) (hE : hayashiIsCQ WE) (M L : ℕ) (hM : 0 < M) (hL : 0 < L)
    (PX : X → ℝ) (hPX : IsLaw PX) (PL : Fin L → ℝ) (hPL : IsLaw PL)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : WiretapCode X B M, UsesLaw PL C ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, hayashiCodeError WB C ≤ 8 * hayashiReliability M L t WB PX) ∧
      Imix (hayashiCompose WE C.encoder) ≤ Real.log (eigenCount (average WE PX)) +
        (Real.log 4 + max (s * petzInfo s WE PX - s * hayashiRenyiEntropy s PL) 0) / s := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
