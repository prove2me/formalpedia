-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_additive_uniform_optimality
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.additive_uniform_optimality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:43:49.371653+00:00
-- url     : https://prove2.me/theorems/ef2e426d-cd49-4a62-9c7c-6c5242a869aa
-- title:
--   Unnumbered (52), Appendix C: uniform input maximizes leakage
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   On a finite additive module, suppose $W_x=U_x\rho U_x^\dagger$, where $\rho$ is a density matrix and $U$ is an actual projective unitary representation. Then
--   $$I_{\rm mix}(W)=I_{\max}(W)=\max_P I(W,P).$$
--   Thus the uniform law attains the maximum over every normalized input law; symmetry is encoded by the projective orbit, not an assumed equality of information quantities.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 7, Unnumbered (52), Appendix C: uniform input maximizes leakage

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

/-- PDF pp.7,29, (52): uniform input attains the information maximum for an actual
projective orbit channel on a finite additive module. -/
theorem additive_uniform_optimality {K G : Type} [Ring K] [AddCommGroup G] [Module K G]
    [Fintype G] [Nonempty E] (W : G → Matrix E E ℂ) (hW : hayashiIsCQ W)
    (hadd : IsAdditiveCQ W) : Imix W = Imax W := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
