-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P43_replacerCapacitiesZero
-- name    : QAlgorithms.Papers.Independent.Advance50.P43.replacerCapacitiesZero
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:11:48.575752+00:00
-- url     : https://prove2.me/theorems/265a2909-1d0c-4bf2-8e2b-6fa245d2b2c4
-- title:
--   All five comparison-replacer capacities vanish
-- statement:
--   Let $Q$ and $B$ be nonzero finite-dimensional registers and let $\omega_B$ be a density matrix. Define the replacer channel $R(X)=\operatorname{Tr}(X)\omega_B$. The symbols $C_1,C,C_P,Q,C_E$ denote, respectively, single-use Holevo capacity, classical capacity, private classical capacity, quantum capacity, and entanglement-assisted classical capacity. The last four are ordinary memoryless capacities with vanishing coding error, in bits or qubits per use; only $C_E$ permits unlimited preshared entanglement, and no additional communication is available.
--
--   Then
--
--   $$C_1(R)=C(R)=C_P(R)=Q(R)=C_E(R)=0.$$
--
--   Applied to $\omega_B=\rho_B^{(1)}(t)$, this is Eq. (27). Input independence makes every capacity vanish even with entanglement assistance.
-- source:
--   Quantum-capacity bounds in spin-network communication channels, arXiv:1905.11920v2, PDF p. 4, §III, Eq.(27)

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

/-- arXiv:1905.11920v2, PDF p.4, (27): all five capacities of a normalized
finite-dimensional comparison replacer vanish. No network/LR premise is needed. -/
theorem replacerCapacitiesZero [Nonempty Q] [Nonempty B]
    (omega : Matrix B B ℂ) (homega : IsDensityMatrix omega) :
    let R : Superop Q B := replacer omega
    holevoCapacity R = 0 ∧ ordinaryClassicalCapacity R = 0 ∧ privateCapacity .actualMarginal (choiDilation R) = 0 ∧
      quantumCapacity R = 0 ∧ resourceCapacity standardEbit R = 0 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P43

end
