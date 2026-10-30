-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_nested_nonuniform_secrecy
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.nested_nonuniform_secrecy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:39:24.212586+00:00
-- url     : https://prove2.me/theorems/d8932d26-df9b-4dde-8424-ddd2854b01fd
-- title:
--   Lemma 12, (134)–(136): non-uniform random linear-code secrecy
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   For a message-output cq channel $V$, $I_{\rm mix}(V)$ and $d_{1,\rm mix}(V)$ are its uniform-message Holevo information and full trace-norm correlation. Their maximum versions optimize over every message law. A code has an actual stochastic encoder and a normalized message POVM; $\epsilon$ and $\epsilon_{\max}$ denote its average and worst-message error. “Uses $P_L$” means each encoder row is a pushforward of that sole auxiliary law under a deterministic table chosen before communication.
--
--   Let $f_Z:A\to X$ be injective linear maps obeying Condition 2, with normalized seed law. For each seed let a subspace $C_{1,Z}$ contain the image and let $M\ge1$ representatives enumerate $C_{1,Z}/f_Z(A)$ once each. Let $P_A$ be any auxiliary law and $Y$ independent uniform on $X$. Encode $m$ by $f_Z(a)+x_{m,Z}+Y$ with $a\sim P_A$. For $0<s\le1$,
--   $$\mathbb E I_{\rm mix}\le\frac{v^s}{s}e^{s(I_s-H_{1+s}(P_A))},$$
--   $$\mathbb E e^{sI_{\rm mix}}\le v^s(1+e^{s(I_s-H_{1+s}(P_A))}),\qquad\mathbb E d_{1,\rm mix}\le2\mu_se^{\frac s2(I_s^G-H_{1+s}(P_A))}.$$
--   The Eve information quantities use uniform ambient input. Condition 2 is the nonzero probability bound $1/(|X|-1)$, not an assumed universal2 property. The missing $s$ in printed (135) is restored; the proof's hashing issue is flagged for independent moderation.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 23, Lemma 12, (134)–(136): non-uniform random linear-code secrecy

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

/-- PDF p.23, Lemma 12, (134)–(136): genuine nonuniform quotient representatives,
Condition 2, independent ambient translation, and the factor two in trace norm.
Correction: restore the missing s in exp(s I_s) in (135), as fixed by (61),(93),(145).
The proof's universal2 claim is separately flagged in MODERATION_NOTES.md. -/
theorem nested_nonuniform_secrecy {K D G : Type} [Field K] [Fintype K]
    [AddCommGroup D] [AddCommGroup G] [Module K D] [Module K G] [Fintype D] [Fintype G]
    [Nonempty E] (WE : G → Matrix E E ℂ) (hE : hayashiIsCQ WE)
    (M : ℕ) (hM : 0 < M) (PA : D → ℝ) (hPA : IsLaw PA)
    (PZ : Z → ℝ) (C : Z → AffinePair K D G M)
    (hf : Condition2 PZ (fun z => (C z).linear)) (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    shiftExpect PZ (fun z y => Imix (affinePairOutput WE PA (C z) y)) ≤ secrecy s WE uniform PA ∧
    shiftExpect PZ (fun z y => Real.exp (s * Imix (affinePairOutput WE PA (C z) y))) ≤
      Real.rpow (eigenCount (average WE uniform)) s *
        (1 + Real.exp (s * (petzInfo s WE uniform - hayashiRenyiEntropy s PA))) ∧
    shiftExpect PZ (fun z y => d1mix (affinePairOutput WE PA (C z) y)) ≤
      2 * traceBound s WE uniform PA := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
