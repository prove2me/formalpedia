-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_phase_cq_information
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.phase_cq_information
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:41:00.108988+00:00
-- url     : https://prove2.me/theorems/39d93227-0ffa-4b5a-84e7-d0a729e652b4
-- title:
--   Unnumbered p.25: explicit phase cq-channel information identities
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   For $d\ge1$, let $P_Z$ be a law on $\mathbb Z_d$ and $p(\cdot\mid z)$ normalized conditional laws, without independence. Set $\omega=e^{2\pi i/d}$,
--   $$|\psi_{j,z}\rangle=\sum_x\omega^{jx}\sqrt{p(x\mid z)}|x,z\rangle,\qquad W_j=\sum_zP_Z(z)|\psi_{j,z}\rangle\langle\psi_{j,z}|.$$
--   These are density matrices, their uniform average is diagonal with entries $P_Z(z)p(x\mid z)$, and for $0\le s\le1$,
--   $$I(W,\rm unif)=H(X\mid Z),\quad I_s(W,\rm unif)=H_{1-s}(X\mid Z),\quad I_s^G(W,\rm unif)=H_{1/(1+s)}(X\mid Z),$$
--   $$e^{sI_s^G}=\left(\sum_zP_Z(z)\sum_xp(x\mid z)^{1/(1+s)}\right)^{1+s}.$$
--   The conditional entropy convention is $H_\alpha(X\mid Z)=\log[\sum_zP_Z(z)\sum_{x:p>0}p(x\mid z)^\alpha]/(1-\alpha)$, with the Shannon limit at one. This is an explicit cq family, without asserting it is the complement of printed (151).
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 25, Unnumbered p.25: explicit phase cq-channel information identities

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

/-- PDF p.25: information identities for the explicitly constructed phase cq
family, independently of the false physical-complement identification. The power
1+s is OUTSIDE the full trace in the Gallager expression. -/
theorem phase_cq_information (d : ℕ) [NeZero d]
    (PZ : ZMod d → ℝ) (hPZ : IsLaw PZ)
    (P : ZMod d → ZMod d → ℝ) (hP : ∀ z, IsLaw (P z))
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    hayashiIsCQ (phaseCQ d PZ P) ∧
    average (phaseCQ d PZ P) uniform =
      Matrix.diagonal (fun u : ZMod d × ZMod d => ((PZ u.2 * P u.2 u.1 : ℝ) : ℂ)) ∧
    holevo uniform (phaseCQ d PZ P) = ∑ z, PZ z * hayashiShannon (P z) ∧
    petzInfo s (phaseCQ d PZ P) uniform = hayashiConditionalRenyi (1 - s) PZ P ∧
    gallagerInfo s (phaseCQ d PZ P) uniform = hayashiConditionalRenyi (1 / (1 + s)) PZ P ∧
    Real.exp (s * gallagerInfo s (phaseCQ d PZ P) uniform) =
      Real.rpow (∑ z, PZ z * ∑ x, Real.rpow (P z x) (1 / (1 + s))) (1 + s) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
