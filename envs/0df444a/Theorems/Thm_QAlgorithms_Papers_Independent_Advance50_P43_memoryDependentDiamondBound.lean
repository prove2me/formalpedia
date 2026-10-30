-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P43_memoryDependentDiamondBound
-- name    : QAlgorithms.Papers.Independent.Advance50.P43.memoryDependentDiamondBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:16:38.894319+00:00
-- url     : https://prove2.me/theorems/124312e1-45a6-4b95-94bf-f84ccefb4101
-- title:
--   Memory-dependent unperturbed-channel inequality chain
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
--   Write $\rho_B^{(0)}(t)=\operatorname{Tr}_{AC}[U(t)\tau_{ABC}U(t)^\dagger]$ and $\Phi_{\mathrm{DP}}^{(0)}(X)=\operatorname{Tr}(X)\rho_B^{(0)}(t)$.
--
--   Let $M_Q=\dim Q$, let $d_1$ be the supremum of the output trace norm over density inputs, and let $\|\cdot\|_\diamond$ be the full reference-assisted channel distance. Then
--
--   $$\|\Phi-\Phi_{\mathrm{DP}}^{(0)}\|_\diamond\le2M_Qd_1(\Phi,\Phi_{\mathrm{DP}}^{(0)})\le2M_QM_A^2\epsilon_{AB}(t).$$
--
--   This retains the complete memory-dependent chain and the original unperturbed comparison channel.
-- source:
--   Quantum-capacity bounds in spin-network communication channels, arXiv:1905.11920v2, PDF p. 6, §III.B, Eq.(45)

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

/-- arXiv:1905.11920v2, PDF p.6, (45): the entire memory-dependent inequality
chain, relative to the unperturbed comparison channel. -/
theorem memoryDependentDiamondBound [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty Q]
    (D : LRData A B C)
    (tau : Matrix (A × (B × C)) (A × (B × C)) ℂ) (htau : IsDensityMatrix tau)
    (E : Superop (Q × A) (Q × A)) (hE : IsChannel E) (t : ℝ) :
    let Phi := snc D tau E t
    let R : Superop Q B := comparisonZero D tau t
    diamond (Phi - R) ≤ 2 * (Fintype.card Q : ℝ) * stateDistance Phi R ∧
      2 * (Fintype.card Q : ℝ) * stateDistance Phi R ≤
        2 * (Fintype.card Q : ℝ) * (Fintype.card A : ℝ) ^ 2 * D.epsilon t := by sorry

end QAlgorithms.Papers.Independent.Advance50.P43

end
