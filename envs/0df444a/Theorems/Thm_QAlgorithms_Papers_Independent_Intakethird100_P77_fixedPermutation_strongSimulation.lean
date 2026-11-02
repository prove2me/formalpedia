-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P77_fixedPermutation_strongSimulation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P77.fixedPermutation_strongSimulation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:16:23.54778+00:00
-- url     : https://prove2.me/theorems/0c3771c4-51b9-47b7-bf50-b43f4cadf5ec
-- title:
--   A single fixed wire permutation preserves strong simulability
-- statement:
--   Let $U_s$ be an effectively uniform circuit of allowable nearest-neighbour matchgates and let $P_s$ implement one effectively described permutation of its wires. Use that same permutation for every gate in the circuit. For arbitrary effectively described normalized product inputs and any existing single output wire, the conjugated circuit $V_s=P_s^\dagger U_sP_s$ admits deterministic strong simulation to $m$ binary digits in polynomial time. A single global reordering restores the complete original circuit:
--
--   $$P_sV_sP_s^\dagger=U_s.$$
--
--   This permits interactions on the edges of one permuted path, while preserving product inputs and one-wire measurements under relabeling. It does not allow a different permutation for each gate.
-- source:
--   Matchgates and classical simulation of quantum circuits, arXiv:0804.4050v2, PDF p. 14, Section 6 Example 1: fixed wire permutations preserve a path of simulatable interactions

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P77

open QAlgorithms

open QAlgorithms.Complexity (Str)

open QAlgorithms.Papers.Independent.Advance50.P19 (Major CARSystem)

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.14 Example 1: one fixed permutation per circuit preserves strong
simulation and a single reordering restores the whole nearest-neighbour
circuit. A separate permutation for each gate is not permitted. -/
theorem fixedPermutation_strongSimulation (F : ParityFamily)
    (I : ProductInputs F.width) (hF : F.Effective) (hI : EffectiveNumbers I.data)
    (hmatch : ∀ s g, g ∈ F.gates s → g.Allowable)
    (hpath : ∀ s, RangeBound 1 (F.gates s))
    (p : (s : Str) → Equiv.Perm (Fin (F.width s)))
    (hp : EffectivePermutations F.width p) :
    StrongSimulation F.width (fun s k b =>
      singleWireProbability
        (star (permutationOperator (p s)) * (parityCircuit (F.gates s)).unitary *
          permutationOperator (p s)) (prodState (I.factor s)) k b) ∧
    (∀ s, permutationOperator (p s) *
        (star (permutationOperator (p s)) * (parityCircuit (F.gates s)).unitary *
          permutationOperator (p s)) * star (permutationOperator (p s)) =
      (parityCircuit (F.gates s)).unitary) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P77

end
