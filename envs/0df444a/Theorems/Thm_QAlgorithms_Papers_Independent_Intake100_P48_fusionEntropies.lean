-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P48_fusionEntropies
-- name    : QAlgorithms.Papers.Independent.Intake100.P48.fusionEntropies
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:24:43.448763+00:00
-- url     : https://prove2.me/theorems/ea1b3c0c-cf59-4c21-b6c7-f86e614c3f0c
-- title:
--   Canonical three- and four-puncture fusion-state entropies
-- statement:
--   Let $\mathcal A$, $N_{ab}^{c}$, $d_a$, conjugation, the vacuum, $D$, and $p_a=d_a^2/D^2$ be the finite rigid fusion data described above. For three punctures use orthonormal basis labels $(a,b,c,\mu)$ with $1\le\mu\le N_{ab}^{\bar c}$, and define the diagonal matrix $\rho_3$ to have eigenvalue $d_ad_bd_c/D^4$ on that basis vector. For four punctures use labels $(a,b,c,d,x,\mu,\nu)$ with $1\le\mu\le N_{ab}^{x}$ and $1\le\nu\le N_{xc}^{\bar d}$, and define $\rho_4$ to have eigenvalue $d_ad_bd_cd_d/D^6$. A zero multiplicity contributes no basis vector. Both matrices are positive semidefinite and have trace one.
--
--   With $S(\rho)=-\operatorname{Tr}(\rho\log\rho)$ in natural logarithms, including $0\log0=0$, their entropies satisfy
--
--   $$
--   S(\rho_3)=4\log D-3\sum_a p_a\log d_a,\qquad
--   S(\rho_4)=6\log D-4\sum_a p_a\log d_a.
--   $$
--
--   These are the canonical finite effective fusion densities used in the TQFT calculation, with normalization and entropy evaluations as conclusions.
-- source:
--   Topological entanglement entropy, arXiv:hep-th/0510092v2, PDF p. 3, Eqs. (12), (14)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P48

open Filter

open scoped Topology ComplexConjugate

attribute [local instance] Classical.propDecidable

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- PDF p.3, (12),(14): entropies of the constructed canonical effective densities.
Both are normalized positive matrices; no spectrum or entropy evaluation is assumed. -/
theorem fusionEntropies (f : FusionData A) :
    QAlgorithms.IsDensityMatrix (threeDensity f) ∧
    QAlgorithms.IsDensityMatrix (fourDensity f) ∧
    (Real.log 2 * QAlgorithms.vnEntropy (threeDensity f)) = 4 * Real.log (totalDimension f.dim) - 3 * meanLogDimension f ∧
    (Real.log 2 * QAlgorithms.vnEntropy (fourDensity f)) = 6 * Real.log (totalDimension f.dim) - 4 * meanLogDimension f := by sorry

end QAlgorithms.Papers.Independent.Intake100.P48

end
