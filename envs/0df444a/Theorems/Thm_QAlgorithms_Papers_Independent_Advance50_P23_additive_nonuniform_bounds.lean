-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_additive_nonuniform_bounds
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.additive_nonuniform_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:40:09.081152+00:00
-- url     : https://prove2.me/theorems/a55ec5ef-e2ca-4c78-980b-6cc258b186b1
-- title:
--   Unnumbered (144)–(146): additive non-uniform secrecy bounds
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   For a message-output cq channel $V$, $I_{\rm mix}(V)$ and $d_{1,\rm mix}(V)$ are its uniform-message Holevo information and full trace-norm correlation. Their maximum versions optimize over every message law. A code has an actual stochastic encoder and a normalized message POVM; $\epsilon$ and $\epsilon_{\max}$ denote its average and worst-message error. “Uses $P_L$” means each encoder row is a pushforward of that sole auxiliary law under a deterministic table chosen before communication.
--
--   Under the genuine nonuniform quotient data and Condition 2 above, suppose Eve's channel is additive. For every seed, both uniform-message Holevo and full trace-norm leakage are invariant under ambient translation. Consequently the unshifted encoder satisfies, for $0<s\le1$,
--   $$\mathbb E_Z I_{\rm mix}\le\frac{v^s}{s}e^{s(I_s-H_{1+s}(P_A))},$$
--   $$\mathbb E_Ze^{sI_{\rm mix}}\le v^s(1+e^{s(I_s-H_{1+s}(P_A))}),\qquad\mathbb E_Zd_{1,\rm mix}\le2\mu_se^{\frac s2(I_s^G-H_{1+s}(P_A))}.$$
--   Here all information quantities use uniform ambient input. Nonuniform mixing retains $I_{\rm mix}$; no equality with $I_{\max}$ is asserted.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 24, Unnumbered (144)–(146): additive non-uniform secrecy bounds

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

/-- PDF p.24, (144)–(146): shift invariance removes translation averaging for
additive Eve, but NONUNIFORM mixing retains Imix, not Imax. -/
theorem additive_nonuniform_bounds {K D G : Type} [Field K] [Fintype K]
    [AddCommGroup D] [AddCommGroup G] [Module K D] [Module K G] [Fintype D] [Fintype G]
    [Nonempty E] (WE : G → Matrix E E ℂ) (hE : hayashiIsCQ WE) (haE : IsAdditiveCQ WE)
    (M : ℕ) (hM : 0 < M) (PA : D → ℝ) (hPA : IsLaw PA)
    (PZ : Z → ℝ) (C : Z → AffinePair K D G M)
    (hf : Condition2 PZ (fun z => (C z).linear)) (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    (∀ z y, Imix (affinePairOutput WE PA (C z) y) = Imix (affinePairOutput WE PA (C z) 0) ∧
      d1mix (affinePairOutput WE PA (C z) y) = d1mix (affinePairOutput WE PA (C z) 0)) ∧
    (∑ z, PZ z * Imix (affinePairOutput WE PA (C z) 0)) ≤ secrecy s WE uniform PA ∧
    (∑ z, PZ z * Real.exp (s * Imix (affinePairOutput WE PA (C z) 0))) ≤
      Real.rpow (eigenCount (average WE uniform)) s *
        (1 + Real.exp (s * (petzInfo s WE uniform - hayashiRenyiEntropy s PA))) ∧
    (∑ z, PZ z * d1mix (affinePairOutput WE PA (C z) 0)) ≤
      2 * traceBound s WE uniform PA := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
