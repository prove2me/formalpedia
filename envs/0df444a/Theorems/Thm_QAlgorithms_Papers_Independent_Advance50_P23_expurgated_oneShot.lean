-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_expurgated_oneShot
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.expurgated_oneShot
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:26:51.498707+00:00
-- url     : https://prove2.me/theorems/1ea03b1e-5d0d-4f48-bd5a-0247726060f1
-- title:
--   Corollary 1, (72)–(74): expurgated source-universal code
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   For a message-output cq channel $V$, $I_{\rm mix}(V)$ and $d_{1,\rm mix}(V)$ are its uniform-message Holevo information and full trace-norm correlation. Their maximum versions optimize over every message law. A code has an actual stochastic encoder and a normalized message POVM; $\epsilon$ and $\epsilon_{\max}$ denote its average and worst-message error. “Uses $P_L$” means each encoder row is a pushforward of that sole auxiliary law under a deterministic table chosen before communication.
--
--   With the two cq channels, input law, positive integers $M,L$, and auxiliary law $P_L$ as above, there is one code using $P_L$ with exactly $K=\lceil M/4\rceil$ messages such that
--   $$\begin{aligned}
--   \epsilon_{\max}&\le48\inf_{0\le t\le1}(ML)^te^{-tI_{-t}(W_B,P_X)},\\
--   I_{\max}&\le12\inf_{0<s\le1}\frac{v^s}{s}e^{-sH_{1+s}(P_L)+sI_s(W_E,P_X)},\\
--   d_{1,\max}&\le24\inf_{0<s\le1}\mu_se^{\frac s2(I_s^G(W_E,P_X)-H_{1+s}(P_L))}.
--   \end{aligned}$$
--   The source prints $M/4$; the integer correction is the proof's lower bound on the number of good messages. The retained decoder is normalized by assigning discarded effects to one retained outcome.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 11, Corollary 1, (72)–(74): expurgated source-universal code

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

/-- PDF p.11, Corollary 1, (72)–(74). Correction: the proof gives at least M/4
messages, so retain exactly ceil(M/4)=(M+3)/4 messages. Add discarded POVM effects
to one retained outcome to restore normalization without increasing any error. -/
theorem expurgated_oneShot [Nonempty X] [Nonempty B] [Nonempty E]
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ)
    (hB : hayashiIsCQ WB) (hE : hayashiIsCQ WE) (M L : ℕ) (hM : 0 < M) (hL : 0 < L)
    (PX : X → ℝ) (hPX : IsLaw PX) (PL : Fin L → ℝ) (hPL : IsLaw PL) :
    ∃ C : WiretapCode X B ((M + 3) / 4), UsesLaw PL C ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, maxError WB C ≤ 48 * hayashiReliability M L t WB PX) ∧
      (∀ s ∈ Set.Ioc (0 : ℝ) 1, Imax (hayashiCompose WE C.encoder) ≤ 12 * secrecy s WE PX PL) ∧
      (∀ s ∈ Set.Ioc (0 : ℝ) 1, d1max (hayashiCompose WE C.encoder) ≤ 24 * traceBound s WE PX PL) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
