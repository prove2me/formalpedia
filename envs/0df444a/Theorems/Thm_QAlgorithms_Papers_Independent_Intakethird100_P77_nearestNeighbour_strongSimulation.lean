-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P77_nearestNeighbour_strongSimulation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P77.nearestNeighbour_strongSimulation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:08:42.28092+00:00
-- url     : https://prove2.me/theorems/913f573d-614f-47c5-ba35-b26ad4524bd6
-- title:
--   Nearest-neighbour matchgates admit strong classical simulation
-- statement:
--   Let a uniformly described circuit family consist of two-qubit parity-block gates $G(A,B)$, where $A,B$ are unitary and $\det A=\det B$, placed only on adjacent wires of a fixed path. Let the input on each wire be an independently normalized one-qubit pure state. Circuit structure, gate entries, and input amplitudes have polynomial-time finite bit descriptions to requested precision. For every existing output wire $k$ and outcome $b\in\{0,1\}$, a single deterministic classical polynomial-time machine computes a dyadic $q$ such that
--
--   $$|q-p_b|\le 2^{-m},\qquad p_b=\frac{1+(-1)^b\langle Z_k\rangle_{\rm out}}2.$$
--
--   The machine is fixed before the instance description, wire, outcome and requested precision $m$. Its time includes the description cost and precision. This is strong simulation of a single final measurement for arbitrary product inputs, including inputs without definite fermionic parity.
-- source:
--   Matchgates and classical simulation of quantum circuits, arXiv:0804.4050v2, PDF p. 2, Theorem 1 / abstract seed: nearest-neighbour matchgate strong simulation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P77

open QAlgorithms

open QAlgorithms.Complexity (Str)

open QAlgorithms.Papers.Independent.Advance50.P19 (Major CARSystem)

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2 Theorem 1, with the precision convention of p.3. Arbitrary
normalized product inputs are allowed. The common phase of an equal-determinant
matchgate is retained; the local Gaussian identification on p.11 requires the
phase correction recorded in HARD.md. -/
theorem nearestNeighbour_strongSimulation (F : ParityFamily)
    (I : ProductInputs F.width) (hF : F.Effective)
    (hI : EffectiveNumbers I.data)
    (hmatch : ∀ s g, g ∈ F.gates s → g.Allowable)
    (hpath : ∀ s, RangeBound 1 (F.gates s)) :
    StrongSimulation F.width (fun s k b =>
      singleWireProbability (parityCircuit (F.gates s)).unitary (prodState (I.factor s)) k b) ∧
    (∀ s (k : Fin (F.width s)) b,
      singleWireProbability (parityCircuit (F.gates s)).unitary (prodState (I.factor s)) k b =
        (1 + (if b then -1 else 1) *
          (outputExpectation (parityCircuit (F.gates s)).unitary
            (prodState (I.factor s)) (zOperator k)).re) / 2) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P77

end
