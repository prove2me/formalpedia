-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P30_single_use_reduction
-- name    : QAlgorithms.Papers.Independent.Gap48.P30.single_use_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:14:49.408146+00:00
-- url     : https://prove2.me/theorems/c2aced37-c971-4e2b-812c-b4db2440fc43
-- title:
--   Single-use reduction: C1 iff C2 iff C3; C4 is sufficient
-- statement:
--   Consider a single use of a phase-insensitive Gaussian channel on the full single-mode Fock space, with vacuum covariance $I$. For $\tau\ge0$ and $\nu\ge|\tau-1|$, write $M_{\tau,\nu}$ for the channel with $K=\sqrt{\tau}I$ and $N=\nu I$. Write $A_G$ for the vacuum-environment amplifier of intensity gain $G\ge1$, and $V_r$ for its two-mode vacuum dilation, where $G=\cosh^2r$, $r\ge0$. All density operators are positive trace-class operators of trace one; all pure input vectors have norm one. Entropy $S$ is in nats and may be infinite, and $E(\psi)=S(\operatorname{Tr}_E|\psi\rangle\langle\psi|)$.
--
--   C1 says that, for every allowed $\tau,\nu$, every coherent input $|\alpha\rangle$ minimizes $S(M_{\tau,\nu}(\rho))$ over all density operators $\rho$. C2 says that, for every $G\ge1$, the vacuum minimizes $S(A_G(|u\rangle\langle u|))$ among centered pure inputs. C3 says that, for every $r\ge0$, the vacuum input minimizes $E(V_r u)$ over the same centered inputs. Centered means that the convergent annihilation-expectation series $\sum_{n\ge0}\sqrt{n+1}\,\overline{u_n}u_{n+1}$ has sum zero. C4 says that the squared Schmidt law of $V_r|0\rangle$ majorizes that of $V_r u$ for every such nonvacuum input, with equality of states understood at the density level. Then
--
--   $$
--   (C1\Longleftrightarrow C2)\;\wedge\;(C2\Longleftrightarrow C3)\;\wedge\;(C4\Longrightarrow C3).
--   $$
--
--   This is a reduction of the single-use minimum-entropy problem. C1 has no energy restriction and no minimizing input is presumed to exist.
-- source:
--   Majorization theory approach to the Gaussian channel minimum entropy conjecture, arXiv:1111.1986v1, PDF p. 2, C1–C4; Appendix 1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P30

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- arXiv:1111.1986v1, PDF pp.1-5, C1-C4 and Appendix 1. Single-use
C1 iff C2 iff C3; C4 is sufficient. No capacity, additivity, finite-energy,
or attainment assertion is made. Eq.(6)'s sign and factor 1/2 are replaced
by the positive Kraus dilation agreeing with A.4 and A.15-A.17. -/
theorem single_use_reduction :
    (Conjecture1 ↔ Conjecture2) ∧ (Conjecture2 ↔ Conjecture3) ∧
      (Conjecture4 → Conjecture3) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P30

end
