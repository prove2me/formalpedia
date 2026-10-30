-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P43_outputDimensionCapacityBounds
-- name    : QAlgorithms.Papers.Independent.Advance50.P43.outputDimensionCapacityBounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:12:38.682756+00:00
-- url     : https://prove2.me/theorems/f79b31ed-2ad8-42b4-8cb1-534c02f37164
-- title:
--   Output-dimension classical and quantum bounds
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
--   Put $M=2\min\{M_A^4,M_A^3M_BM_C\}$ and $M'=\min\{M_A,M_B\}$. Here $g(x)=(1+x)H_2(x/(1+x))$ for $x\geq0$, with $g(0)=0$ and $H_2(p)=-p\log_2p-(1-p)\log_2(1-p)$, interpreting $0\log_20=0$. The symbols $C_1,C,C_P,Q,C_E$ denote, respectively, single-use Holevo capacity, classical capacity, private classical capacity, quantum capacity, and entanglement-assisted classical capacity. The last four are ordinary memoryless capacities with vanishing coding error, in bits or qubits per use; only $C_E$ permits unlimited preshared entanglement, and no additional communication is available.
--
--   Both capacities obey
--
--   $$Q(\Phi),\ C(\Phi)\le M\epsilon_{AB}(t)\log_2 M_B+g(M\epsilon_{AB}(t)/2).$$
--
--   This preliminary output-dimension estimate is retained separately from the final bound.
-- source:
--   Quantum-capacity bounds in spin-network communication channels, arXiv:1905.11920v2, PDF p. 4, §III, Eq.(28)

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

/-- arXiv:1905.11920v2, PDF p.4, (28): preliminary output-dimension bounds. -/
theorem outputDimensionCapacityBounds [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty Q]
    (D : LRData A B C)
    (tau : Matrix (A × (B × C)) (A × (B × C)) ℂ) (htau : IsDensityMatrix tau)
    (E : Superop (Q × A) (Q × A)) (hE : IsChannel E) (t : ℝ) :
    let delta := dimensionConstant A B C * D.epsilon t
    let bound := delta * Real.logb 2 (Fintype.card B) + continuityG (delta / 2)
    quantumCapacity (snc D tau E t) ≤ bound ∧
      ordinaryClassicalCapacity (snc D tau E t) ≤ bound := by sorry

end QAlgorithms.Papers.Independent.Advance50.P43

end
