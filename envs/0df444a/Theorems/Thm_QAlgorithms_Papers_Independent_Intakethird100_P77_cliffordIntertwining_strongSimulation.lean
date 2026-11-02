-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P77_cliffordIntertwining_strongSimulation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P77.cliffordIntertwining_strongSimulation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:15:47.849524+00:00
-- url     : https://prove2.me/theorems/a01e135f-a26e-4fb9-bb1d-ccb10fa086f6
-- title:
--   Fixed-degree Clifford-intertwined Gaussian circuits and their boundary interpretation
-- statement:
--   For each circuit instance $s$, choose a fixed Clifford unitary $T_s$ normalizing the full phase-inclusive Pauli group and define $c'_i=T_s^\dagger c_iT_s$ from the Jordan–Wigner generators. Select one existing measured wire $k_s$ and supply a canonical polynomial for $Z_{k_s}$ in the $c'_i$ of degree at most one fixed $d$. Supply effective product factors of all $c'_i$, real skew Gaussian coefficients, normalized product inputs and the selected observable coefficients. All structural and numerical description costs are charged. Other wires need no bounded-degree polynomial representation. The resulting circuit has one deterministic polynomial-time simulator for its selected bit probabilities to error $2^{-m}$.
--
--   Writing $U_{\rm new}=T_s^\dagger U_{\rm old}T_s$ and $\psi_s$ for the product input, the exact boundary interpretation is
--
--   $$\langle U_{\rm new}\psi_s,Z_{k_s}U_{\rm new}\psi_s\rangle=\langle U_{\rm old}T_s\psi_s,(T_sZ_{k_s}T_s^\dagger)U_{\rm old}T_s\psi_s\rangle.$$
--
--   The Clifford is fixed across all gates in an instance; it need not be Gaussian or local. The transformed input can be entangled, and the transformed observable can involve many wires.
-- source:
--   Matchgates and classical simulation of quantum circuits, arXiv:0804.4050v2, PDF p. 13, Section 6: Clifford-conjugated Gaussian simulation and boundary interpretation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P77

open QAlgorithms

open QAlgorithms.Complexity (Str)

open QAlgorithms.Papers.Independent.Advance50.P19 (Major CARSystem)

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.12--13: constant-degree Clifford intertwining gives strong simulation
for the selected output and the exact boundary interpretation. The old input
is T psi and the old observable T Z_k T† at that output. Other output wires need
not satisfy the degree condition; T is not required to be Gaussian or local. -/
theorem cliffordIntertwining_strongSimulation (d : ℕ) (F : IntertwinedFamily)
    (I : ProductInputs F.base.width) (hF : F.Effective)
    (hI : EffectiveNumbers I.data)
    (hdegree : ∀ s, (F.observable s).DegreeLE d) :
    SelectedStrongSimulation (fun s b =>
      singleWireProbability
        (gaussianCircuit (conjugatedGenerators (F.T s) (jordanWigner (F.base.width s)))
          (F.base.gates s)) (prodState (I.factor s)) (F.measured s) b) ∧
    (∀ s,
      outputExpectation
          (gaussianCircuit (conjugatedGenerators (F.T s) (jordanWigner (F.base.width s)))
            (F.base.gates s)) (prodState (I.factor s)) (zOperator (F.measured s)) =
        outputExpectation (gaussianCircuit (jordanWigner (F.base.width s)) (F.base.gates s))
          (act (F.T s : Op (Qubits (F.base.width s))) (prodState (I.factor s)))
          ((F.T s : Op (Qubits (F.base.width s))) * zOperator (F.measured s) *
            star (F.T s : Op (Qubits (F.base.width s))))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P77

end
