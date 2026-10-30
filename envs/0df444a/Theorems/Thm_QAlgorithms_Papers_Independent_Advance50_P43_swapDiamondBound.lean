-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P43_swapDiamondBound
-- name    : QAlgorithms.Papers.Independent.Advance50.P43.swapDiamondBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:17:25.66499+00:00
-- url     : https://prove2.me/theorems/0442c242-01d2-4223-9e90-aa2c30e41459
-- title:
--   Swap-in/swap-out diamond-distance bound
-- statement:
--   Let $A,B,C$ be the disjoint nonzero finite spin registers, with dimensions $M_A,M_B,M_C$, let $H=H^\dagger$ be their fixed network Hamiltonian, set $U(t)=e^{-iHt}$, and let $\epsilon_{AB}(t)\ge0$ be an even state-independent operator-norm bound $\|[U(t)^\dagger X_AU(t),Y_B]\|\le\epsilon_{AB}(t)\|X_A\|\|Y_B\|$ for every supported $X_A,Y_B$. Let the arbitrary density matrix $\tau_{ABC}$ satisfy the finite-network and state-independent LR assumptions of Eqs. (2)–(6); all register dimensions are positive. An input memory isomorphic to $A$ is swapped into $A$ at time zero. Let $M_A=\dim A$ and $\tau_{BC}=\operatorname{Tr}_A\tau_{ABC}$. The resulting map is $\Phi_{\rm SW}(\rho_A)=\operatorname{Tr}_{AC}[U(t)(\rho_A\otimes\tau_{BC})U(t)^\dagger]$, while $\Phi_{\rm DP}^{(0)}(X)=\operatorname{Tr}(X)\operatorname{Tr}_{AC}[U(t)\tau_{ABC}U(t)^\dagger]$. Then, in the full diamond distance,
--
--   $$\|\Phi_{\rm SW}-\Phi_{\rm DP}^{(0)}\|_\diamond\le2M_A^3\epsilon_{AB}(t).$$
--
--   The swap itself creates the product input to the network; the original state is allowed to be correlated. No further swap-specific capacity formula is asserted.
-- source:
--   Quantum-capacity bounds in spin-network communication channels, arXiv:1905.11920v2, PDF p. 6, §III.B, Eq.(46)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P43

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45
  (holevoCapacity resourceCapacity standardEbit)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer diamond)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst privateCapacity)

open QAlgorithms.Papers.Independent.Information100.P22 (quantumCapacity)

open QAlgorithms.Papers.Independent.Dependency50.P23 (ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

variable {A B C Q : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype Q]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq Q]

/-- arXiv:1905.11920v2, PDF p.6, (46): swap input has dimension MA and the
comparison remains DP^(0). No product assumption is imposed on original tau. -/
theorem swapDiamondBound [Nonempty A] [Nonempty B] [Nonempty C]
    (D : LRData A B C)
    (tau : Matrix (A × (B × C)) (A × (B × C)) ℂ) (htau : IsDensityMatrix tau)
    (t : ℝ) :
    diamond (swapChannel D tau t - comparisonZero D tau t) ≤
      2 * (Fintype.card A : ℝ) ^ 3 * D.epsilon t := by sorry

end QAlgorithms.Papers.Independent.Advance50.P43

end
