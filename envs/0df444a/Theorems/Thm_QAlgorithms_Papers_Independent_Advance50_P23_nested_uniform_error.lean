-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_nested_uniform_error
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.nested_uniform_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:36:37.204309+00:00
-- url     : https://prove2.me/theorems/ecf4067e-cc5e-4dfb-afe9-fb272cb40ade
-- title:
--   Lemma 10, (112): uniform random linear-code decoding error
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   For a message-output cq channel $V$, $I_{\rm mix}(V)$ and $d_{1,\rm mix}(V)$ are its uniform-message Holevo information and full trace-norm correlation. Their maximum versions optimize over every message law. A code has an actual stochastic encoder and a normalized message POVM; $\epsilon$ and $\epsilon_{\max}$ denote its average and worst-message error. “Uses $P_L$” means each encoder row is a pushforward of that sole auxiliary law under a deterministic table chosen before communication.
--
--   For the same actual nested-subspace data with sizes $L,ML$, assume instead Condition 1 on the outer code: $\Pr[x\in C_{1,Z}]\le ML/|X|$ for nonzero $x$. There exist normalized codeword POVMs, grouped into the quotient-message POVMs, such that for every $0<s\le1$,
--   $$\mathbb E_{Z,Y}\epsilon(W_B\mid\Phi_{C_{1,Z}+Y,C_{2,Z}})\le4(ML)^se^{-sI_{-s}(W_B,\rm unif)}.$$
--   The decoder is existential; the claim does not cover arbitrary POVMs. No randomization condition on the inner code is required.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 20, Lemma 10, (112): uniform random linear-code decoding error

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

/-- PDF pp.20–21, Lemma 10, (112): suitable normalized codeword POVMs EXIST.
The only ensemble constraint is Condition 1 on C1; arbitrary POVMs are not promised. -/
theorem nested_uniform_error {K G : Type} [Field K] [Fintype K] [AddCommGroup G]
    [Module K G] [Fintype G] [Nonempty B]
    (WB : G → Matrix B B ℂ) (hB : hayashiIsCQ WB) (M L : ℕ) (hM : 0 < M) (hL : 0 < L)
    (PZ : Z → ℝ) (C : Z → NestedPair K G M L)
    (houter : Condition1 PZ (fun z => (C z).outer) (M * L)) :
    ∃ D : Z → G → WiretapCode G B M,
      (∀ z y, GroupedDecoder (C z) y (D z y)) ∧
      ∀ s ∈ Set.Ioc (0 : ℝ) 1,
        shiftExpect PZ (fun z y => hayashiCodeError WB (D z y)) ≤ 4 * hayashiReliability M L s WB uniform := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
