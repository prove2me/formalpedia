-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_canonicalWeakComplements
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.canonicalWeakComplements
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:11:44.832691+00:00
-- url     : https://prove2.me/theorems/34508d46-7363-4326-aad5-f234acffee4f
-- title:
--   All chosen canonical weak complements
-- statement:
--   Use the six canonical forms $A_1,A_2,B_1,B_2,C,D$ of Table 1 on the full one-mode Fock space. Their noise parameter is $N\ge0$; the amplitude $\kappa$ is positive for $C,D$, and $\kappa
--   e1$ for $C$. The $B_1$ noise is fixed to $\operatorname{diag}(0,1/2)$, and $B_2(0)$ is the identity. Use the exact Appendix-A implementer and the selected thermal environment, with vacuum for $B_1$. Put $s=N+1/2$. The weak-complement data $(\widetilde K,\widetilde\alpha)$ are
--
--   $$\begin{array}{c|cc|c}c&\widetilde K&\widetilde\alpha&\text{class}\\\hline A_1&I&0&B_2\\A_2&I&\operatorname{diag}(0,s)&B_1\\B_1&\operatorname{diag}(1,0)&I/2&A_2\\C,\kappa<1&\sqrt{1-\kappa^2}I&\kappa^2sI&C\\C,\kappa>1&\sqrt{\kappa^2-1}\sigma_3&\kappa^2sI&D\\D&\sqrt{\kappa^2+1}I&\kappa^2sI&C\end{array}$$
--
--   All displacements vanish, and each map is Gaussian CPTP. Here $\sigma_3=\operatorname{diag}(1,-1)$. In the $A_2$ row, $B_1$ denotes canonical class, with the displayed environmental noise kept before its canonical squeeze. This is a classification of the specified representations, not uniqueness over all dilations.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 14, §3.1; Table 2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P49

noncomputable section

open scoped BigOperators ENNReal Topology

open Filter MeasureTheory

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

namespace QAlgorithms.Papers.Independent.Claimed50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Table 2, PDF pp.13-15: all chosen canonical weak complements, with A2's
unnormalized B1 noise retained in its actual environment coordinates. -/
theorem canonicalWeakComplements (c : CanonicalClass) (k N : ℝ)
    (hvalid : ValidSourceCanonical c k N) (hnotB2 : c ≠ .B2)
    (U : JointUnitary) (hU : ImplementsJointGaussian U (appendixCouplingMatrix c k))
    (sigma : State ℕ) (hsigma : IsThermal sigma.coefficients (environmentNumber c N)) :
    IsGaussianChannel (weakComplement U sigma.coefficients) (complementData c k N) ∧
    classOf (complementData c k N) =
      (match c with
      | .A1 => .B2
      | .A2 => .B1
      | .B1 => .A2
      | .B2 => .B2
      | .C => if k < 1 then .C else .D
      | .D => .C) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
