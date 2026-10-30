-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P43_memoryIndependentDiamondBound
-- name    : QAlgorithms.Papers.Independent.Advance50.P43.memoryIndependentDiamondBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:11:06.895471+00:00
-- url     : https://prove2.me/theorems/7ae9a29d-c1dd-4c2a-9e34-096029449f95
-- title:
--   Memory-independent diamond-norm bound
-- statement:
--   Let $A,B,C$ be the nonzero finite-dimensional spin registers in the source's fixed network, with Alice and Bob controlling disjoint separated regions $A$ and $B$. Write $M_A,M_B,M_C$ for their dimensions; an empty remaining region $C$ has dimension one. Fix the self-adjoint network Hamiltonian $H$, set $U(t)=e^{-iHt}$, and suppose the nonnegative even function $\epsilon_{AB}$ bounds all supported commutators in operator norm:
--
--   $$
--   \|[U(t)^\dagger X_AU(t),Y_B]\|\leq\epsilon_{AB}(t)\|X_A\|\|Y_B\|.
--   $$
--
--   Let $\tau_{ABC}$ be any density matrix, including correlated mixed states. Let $Q$ be an arbitrary nonzero finite memory register, initially independent of $\tau_{ABC}$, and let $\mathcal E_{QA}$ be any fixed CPTP encoding acting only on $QA$. The induced channel is
--
--   $$
--   \Phi(\rho_Q)=\operatorname{Tr}_{QAC}\!\left[U(t)(\mathcal E_{QA}\otimes\mathrm{id}_{BC})(\rho_Q\otimes\tau_{ABC})U(t)^\dagger\right].
--   $$
--
--   Write $\tau_A=\operatorname{Tr}_{BC}\tau_{ABC}$, $\tau_{BC}=\operatorname{Tr}_A\tau_{ABC}$, $\rho_B^{(1)}(t)=\operatorname{Tr}_{AC}[U(t)(\tau_A\otimes\tau_{BC})U(t)^\dagger]$, and $\Phi_{\mathrm{DP}}^{(1)}(X)=\operatorname{Tr}(X)\rho_B^{(1)}(t)$. Put $M=2\min\{M_A^4,M_A^3M_BM_C\}$ and $M'=\min\{M_A,M_B\}$.
--
--   The full channel diamond distance uses an untouched reference isomorphic to $Q$ and normalized joint pure inputs. Then
--
--   $$\|\Phi-\Phi_{\mathrm{DP}}^{(1)}\|_\diamond\le M\epsilon_{AB}(t).$$
--
--   This is the central memory-independent estimate: neither $M$ nor the LR bound depends on the external memory or encoding.
-- source:
--   Quantum-capacity bounds in spin-network communication channels, arXiv:1905.11920v2, PDF p. 4, §III / §III.B, Eqs.(25)–(26),(70)

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

/-- arXiv:1905.11920v2, PDF p.4, (25)--(26), proved pp.6--7, (70): full diamond
bound independent of external memory, with arbitrary mixed/correlated tau. -/
theorem memoryIndependentDiamondBound [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty Q]
    (D : LRData A B C)
    (tau : Matrix (A × (B × C)) (A × (B × C)) ℂ) (htau : IsDensityMatrix tau)
    (E : Superop (Q × A) (Q × A)) (hE : IsChannel E) (t : ℝ) :
    diamond (snc D tau E t - comparisonOne D tau t) ≤
      dimensionConstant A B C * D.epsilon t := by sorry

end QAlgorithms.Papers.Independent.Advance50.P43

end
