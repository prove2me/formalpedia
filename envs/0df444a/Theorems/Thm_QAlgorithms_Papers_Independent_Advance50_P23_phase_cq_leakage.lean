-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_phase_cq_leakage
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.phase_cq_leakage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:41:34.207976+00:00
-- url     : https://prove2.me/theorems/10d44390-8bd6-4923-8feb-8bcbfd9543f2
-- title:
--   Unnumbered (156)–(160): correlated-error cq leakage bounds and exponents
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   For a message-output cq channel $V$, $I_{\rm mix}(V)$ and $d_{1,\rm mix}(V)$ are its uniform-message Holevo information and full trace-norm correlation. Their maximum versions optimize over every message law. A code has an actual stochastic encoder and a normalized message POVM; $\epsilon$ and $\epsilon_{\max}$ denote its average and worst-message error. “Uses $P_L$” means each encoder row is a pushforward of that sole auxiliary law under a deterministic table chosen before communication.
--
--   Use the explicit phase cq family above and a Condition 1 inner-code ensemble in $\mathbb Z_d$, with compatible finite-field vector-space structure, actual nested sizes $L,ML$, and uniform-coset encoding. For $0<s\le1$,
--   $$\mathbb E I_{\max}\le\frac{v^s e^{sH_{1-s}(X\mid Z)}}{L^ss},\quad\mathbb E e^{sI_{\max}}\le v^s(1+L^{-s}e^{sH_{1-s}(X\mid Z)}),$$
--   $$\mathbb E d_{1,\rm mix}\le\frac{2\mu_s e^{\frac s2H_{1/(1+s)}(X\mid Z)}}{L^{s/2}}.$$
--   For a nonnegative sacrifice rate $R$,
--   $$e_R=\max_{0\le s\le1}s(R-H_{1-s}(X\mid Z)),\quad e_G=\max_{0\le s\le1}\frac s2(R-H_{1/(1+s)}(X\mid Z)).$$
--   Both are positive when $R>H(X\mid Z)$. Conditional Rényi entropy has the averaged-power convention defined above. No independence of error coordinates or physical-complement identification is assumed.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 25, Unnumbered (156)–(160): correlated-error cq leakage bounds and exponents

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

/-- PDF pp.25–26, (156)–(160): correlated-error cq secrecy and exponents. No
independence of the two error coordinates is imposed. Closed-interval objectives
have value zero at s=0, also when the sacrifice rate lies below entropy. -/
theorem phase_cq_leakage {K : Type} [Field K] [Fintype K] (d : ℕ) [NeZero d]
    [Module K (ZMod d)] (PZ : ZMod d → ℝ) (hPZ : IsLaw PZ)
    (P : ZMod d → ZMod d → ℝ) (hP : ∀ z, IsLaw (P z))
    (M L : ℕ) (hM : 0 < M) (hL : 0 < L)
    (seed : Z → ℝ) (C : Z → NestedPair K (ZMod d) M L)
    (hC : Condition1 seed (fun z => (C z).inner) L)
    (R : ℝ) (hR : 0 ≤ R) :
    (∀ s ∈ Set.Ioc (0 : ℝ) 1,
      (∑ z, seed z * Imax (pairOutput (phaseCQ d PZ P) (C z) 0)) ≤
        Real.rpow (eigenCount (average (phaseCQ d PZ P) uniform)) s *
          Real.exp (s * hayashiConditionalRenyi (1 - s) PZ P) / (Real.rpow L s * s) ∧
      (∑ z, seed z * Real.exp (s * Imax (pairOutput (phaseCQ d PZ P) (C z) 0))) ≤
        Real.rpow (eigenCount (average (phaseCQ d PZ P) uniform)) s *
          (1 + Real.exp (s * hayashiConditionalRenyi (1 - s) PZ P) / Real.rpow L s) ∧
      (∑ z, seed z * d1mix (pairOutput (phaseCQ d PZ P) (C z) 0)) ≤
        2 * hayashiMu s (phaseCQ d PZ P) uniform *
          Real.exp (s / 2 * hayashiConditionalRenyi (1 / (1 + s)) PZ P) / Real.rpow L (s / 2)) ∧
    exponentR R (phaseCQ d PZ P) uniform =
      sSup {y : ℝ | ∃ s ∈ Set.Icc (0 : ℝ) 1, y = s * (R - hayashiConditionalRenyi (1 - s) PZ P)} ∧
    exponentG R (phaseCQ d PZ P) uniform =
      sSup {y : ℝ | ∃ s ∈ Set.Icc (0 : ℝ) 1, y = s / 2 * (R - hayashiConditionalRenyi (1 / (1 + s)) PZ P)} ∧
    ((∑ z, PZ z * hayashiShannon (P z)) < R →
      0 < exponentR R (phaseCQ d PZ P) uniform ∧ 0 < exponentG R (phaseCQ d PZ P) uniform) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
