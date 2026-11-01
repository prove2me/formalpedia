-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P13_noisyTeleport_general
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P13.noisyTeleport_general
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:52:26.831261+00:00
-- url     : https://prove2.me/theorems/91c04e8d-670e-45bc-bc2f-224f7323108d
-- title:
--   General noisy-teleportation channel
-- statement:
--   Let $\tau$ be any positive semidefinite two-qubit matrix of trace one. Fix the Bell outcomes $(\Phi^+,\Psi^+,\Psi^-,\Phi^-)$, the corrections $(I,X,Y,Z)$, and a conditional law $p(l\mid k)\ge0$ with $\sum_l p(l\mid k)=1$ for each $k$. The resource and law are independent of the input, and every Bell branch is retained. Write $b_i=\operatorname{Tr}[(I\otimes\sigma_i)\tau]$ and $t_{ji}=\operatorname{Tr}[(\sigma_j\otimes\sigma_i)\tau]$ for $i,j=1,2,3$. Define $t'_{0i}=b_i$ and $t'_{ji}=t_{ji}$ for $j>0$. The resulting operation is a quantum channel with Bloch action
--
--   $$r'_i=f_{i0}+\sum_{j=1}^3 f_{ij}r_j,\qquad f_{ij}=t'_{ji}S_{ij},\qquad S_{ij}=\frac14\sum_{k,l=0}^3(-1)^{\delta_{k0}+\delta_{j2}+\delta_{j0}+\delta_{kj}+\delta_{il}+\delta_{0l}}p(l\mid k).$$
--
--   Here $i=1,2,3$, $j=0,1,2,3$, $\delta$ is the Kronecker delta, and $r$ is any Bloch vector with $\|r\|_2\le1$. This identifies the full affine channel produced by the physical protocol.
-- source:
--   Simulation of non-Pauli Channels, arXiv:1706.05384v2, PDF p. 5, Theorem 11, Eqs.(37)–(39)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P13

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1706.05384v2 PDF p.5, Theorem 11 and Eqs.(37)--(39).
The physical Bell instrument is characterized; no affine-form hypothesis is assumed. -/
theorem noisyTeleport_general (tau : ResourceOp) (htau : IsDensityMatrix tau)
    (p : Fin 4 → Fin 4 → ℝ) (hp : ClassicalTeleportationLaw p) :
    IsChannel (noisyTeleport tau p) ∧ noisyTeleport tau p =
      QAlgorithms.QubitChannels.blochAffineMap
        (fun i => fCoordinate tau p i 0)
        (fun i j => fCoordinate tau p i j.succ) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P13

end
