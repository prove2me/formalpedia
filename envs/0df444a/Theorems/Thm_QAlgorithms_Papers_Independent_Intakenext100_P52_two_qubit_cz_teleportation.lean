-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_two_qubit_cz_teleportation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.two_qubit_cz_teleportation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:33:31.679167+00:00
-- url     : https://prove2.me/theorems/7c347bd6-4e4f-4dcf-ac0d-17e6db51f71c
-- title:
--   §2: CZ teleportation in dimension four
-- statement:
--   On a two-qubit register let $P_a=X^{a_x}Z^{a_z}$, with $a=(a_x,a_z)$ a pair of bits, and put $U_{ab}=(P_a\otimes P_b)CZ$. Let $|\phi_4\rangle=\frac12\sum_{i,j}|i,j\rangle_A|i,j\rangle_B$. This resource equals two Bell pairs after regrouping their halves into Alice's register and Bob's register. The sixteen kets $(U_{ab}^\dagger\otimes I)|\phi_4\rangle$ are orthonormal, and for every normalized two-qubit input,
--
--   $$ |b_{ab}\rangle=\frac14(P_a\otimes P_b)CZ|\psi\rangle,\qquad \Pr(a,b)=\frac1{16}. $$
--
--   The output $4|b_{ab}\rangle$ is normalized. Using real $I,X,Z,XZ$ Pauli representatives pins the branch phases; replacing $XZ$ by $Y$ changes only a scalar phase.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 4, §2: CZ teleportation in dimension four

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Dimension-four CZ teleportation, PDF p.4. The paired Bell resource is explicitly
reindexed as (Alice first-qubit, Alice second-qubit; Bob first-qubit, Bob second-qubit).
Real I,X,Z,XZ representatives pin branch phases; Y differs by an irrelevant scalar. -/
theorem two_qubit_cz_teleportation :
    (∀ a b c d : Bool, finiteMaxEntangled QubitPair ((a,b),(c,d)) =
      finiteMaxEntangled Bool (a,c) * finiteMaxEntangled Bool (b,d)) ∧
    Orthonormal ℂ (fun p : QubitPair × QubitPair => rotatedEntangledKet (czTeleportGate p.1 p.2)) ∧
    ∀ (psi : Vec QubitPair), IsState psi → ∀ a b : QubitPair,
      let v := teleportContraction psi (finiteMaxEntangled QubitPair)
        (rotatedEntangledKet (czTeleportGate a b))
      v = (1 / 4 : ℂ) • act (czTeleportGate a b) psi ∧
      ‖v‖ ^ 2 = (1 / 16 : ℝ) ∧ (4 : ℂ) • v = act (czTeleportGate a b) psi := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
