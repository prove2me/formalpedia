-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_additive_uniform_bounds
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.additive_uniform_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:37:20.296402+00:00
-- url     : https://prove2.me/theorems/09c315aa-510c-4ce1-a312-4530632808c8
-- title:
--   Unnumbered (120)–(125): additive linear-code bounds
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   For a message-output cq channel $V$, $I_{\rm mix}(V)$ and $d_{1,\rm mix}(V)$ are its uniform-message Holevo information and full trace-norm correlation. Their maximum versions optimize over every message law. A code has an actual stochastic encoder and a normalized message POVM; $\epsilon$ and $\epsilon_{\max}$ denote its average and worst-message error. “Uses $P_L$” means each encoder row is a pushforward of that sole auxiliary law under a deterministic table chosen before communication.
--
--   Let both receiver and Eve channels be projective unitary orbits on a finite vector space and let a normalized seed law choose genuine nested codes of sizes $L,ML$. For every seed and ambient shift $y$, the uniform-coset encoder has shift-independent $I_{\rm mix}$ and $d_{1,\rm mix}$, and
--   $$I_{\max}=I_{\rm mix}.$$
--   If $C_2$ obeys Condition 1, then for $0<s\le1$ the unshifted ensemble satisfies
--   $$\mathbb E I_{\max}\le\frac{v^se^{sI_s}}{L^ss},\qquad\mathbb E e^{sI_{\max}}\le v^s(1+L^{-s}e^{sI_s}),\qquad\mathbb E d_{1,\rm mix}\le\frac{2\mu_se^{sI_s^G/2}}{L^{s/2}}.$$
--   If $C_1$ obeys Condition 1, suitable normalized grouped decoders exist with equal translated errors and $\mathbb E\epsilon\le4(ML)^se^{-sI_{-s}(W_B,\rm unif)}$. Eve's information quantities use uniform ambient input. The missing factor $s$ in printed (123) is restored.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 21, Unnumbered (120)–(125): additive linear-code bounds

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

/-- PDF p.21, (120)–(125): orbit shift invariance, source-universal equality,
corrected exp(s I_s) in (123), and existential covariant decoding. C2 and C1
randomization are attached to secrecy and error respectively. -/
theorem additive_uniform_bounds {K G : Type} [Field K] [Fintype K] [AddCommGroup G]
    [Module K G] [Fintype G] [Nonempty B] [Nonempty E]
    (WB : G → Matrix B B ℂ) (WE : G → Matrix E E ℂ)
    (hB : hayashiIsCQ WB) (hE : hayashiIsCQ WE) (haB : IsAdditiveCQ WB) (haE : IsAdditiveCQ WE)
    (M L : ℕ) (hM : 0 < M) (hL : 0 < L) (PZ : Z → ℝ) (hPZ : IsLaw PZ)
    (C : Z → NestedPair K G M L) :
    (∀ z y, Imix (pairOutput WE (C z) y) = Imix (pairOutput WE (C z) 0) ∧
      d1mix (pairOutput WE (C z) y) = d1mix (pairOutput WE (C z) 0) ∧
      Imax (pairOutput WE (C z) y) = Imix (pairOutput WE (C z) y)) ∧
    (Condition1 PZ (fun z => (C z).inner) L → ∀ s ∈ Set.Ioc (0 : ℝ) 1,
      (∑ z, PZ z * Imax (pairOutput WE (C z) 0)) ≤
        Real.rpow (eigenCount (average WE uniform)) s * Real.exp (s * petzInfo s WE uniform) /
          (Real.rpow L s * s) ∧
      (∑ z, PZ z * Real.exp (s * Imax (pairOutput WE (C z) 0))) ≤ uniformMomentBound L s WE uniform ∧
      (∑ z, PZ z * d1mix (pairOutput WE (C z) 0)) ≤ 2 * uniformTraceBound L s WE uniform) ∧
    (Condition1 PZ (fun z => (C z).outer) (M * L) →
      ∃ D : Z → G → WiretapCode G B M, (∀ z y, GroupedDecoder (C z) y (D z y)) ∧
      (∀ z y, hayashiCodeError WB (D z y) = hayashiCodeError WB (D z 0)) ∧
      ∀ s ∈ Set.Ioc (0 : ℝ) 1,
        (∑ z, PZ z * hayashiCodeError WB (D z 0)) ≤ 4 * hayashiReliability M L s WB uniform) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
