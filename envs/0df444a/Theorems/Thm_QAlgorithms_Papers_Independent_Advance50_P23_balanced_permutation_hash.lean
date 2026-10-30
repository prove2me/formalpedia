-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_balanced_permutation_hash
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.balanced_permutation_hash
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T12:44:32.806494+00:00
-- url     : https://prove2.me/theorems/d1eaceea-3d99-4821-8c6a-3146ae1b66b4
-- title:
--   Unnumbered Appendix D: balanced-map random permutations are universal2
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   Let $A,D$ be finite nonempty sets and let $f:A\to D$ have balanced fibres: every fibre has size $|A|/|D|$, equivalently $|f^{-1}(d)|\,|D|=|A|$. Sample $g$ uniformly from all permutations of $A$. Then
--   $$\Pr_g[f(g(a))=f(g(b))]\le1/|D|\qquad(a\ne b).$$
--   Thus $\{f\circ g\}$ is universal2. Balance includes the necessary divisibility; for singleton $A$ the distinct-pair condition is vacuous.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 30, Unnumbered Appendix D: balanced-map random permutations are universal2

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

/-- PDF p.30, Appendix D: a balanced fixed map composed with a uniform permutation
is universal2. Singleton A is allowed, with no distinct input pairs. -/
theorem balanced_permutation_hash {D : Type} [Fintype D] [Nonempty D] [Nonempty A]
    (f : A → D) (hbalanced : hayashiBalanced f) :
    Universal2 (uniform : Equiv.Perm A → ℝ) (fun g a => f (g a)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
