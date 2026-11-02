-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P77_rangeTwo_encodedUniversality
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P77.rangeTwo_encodedUniversality
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:09:30.25682+00:00
-- url     : https://prove2.me/theorems/fe9031ca-8fd9-44ec-9da8-b78a5106291f
-- title:
--   Exact encoded range-two matchgate simulation
-- statement:
--   Present a uniform circuit family using nearest-neighbour controlled-$Z$ gates and arbitrary one-qubit unitary gates, with one final computational-basis measurement on the first wire. Assume effective finite numerical descriptions of its one-qubit gates. There is an absolute constant $C>0$ and an effectively uniform target family on four physical wires per logical wire, fixed before the logical input, such that
--
--   $$|G_s|\le C|C_s|,\qquad \operatorname{range}(G_s)\le2,\qquad p_b(G_s,E_4\psi,1)=p_b(C_s,\psi,1).$$
--
--   Here $s$ is the classical family parameter, $|C_s|$ is its actual gate count, $\psi$ is any normalized logical input, $b$ is either outcome, and $E_4$ linearly extends $|0\rangle\mapsto|0000\rangle$, $|1\rangle\mapsto|1001\rangle$. Every target gate is an allowable equal-determinant matchgate. The constant overhead is relative to the stated source presentation; this is universality with encoding.
-- source:
--   Matchgates and classical simulation of quantum circuits, arXiv:0804.4050v2, PDF p. 4, Theorem 2: encoded universality at range two

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P77

open QAlgorithms

open QAlgorithms.Complexity (Str)

open QAlgorithms.Papers.Independent.Advance50.P19 (Major CARSystem)

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.4--6 Theorem 2: uniform encoded range-two simulation with a universal
constant gate overhead in the source nearest-neighbour CZ/one-qubit normal
form. Printed: any uniform circuit family with constant size increase. Changed:
measure size in the normal form fixed by the source proof on p.4, since
arbitrary-connectivity routing need not have constant cost. The target family is fixed before all logical inputs. Only the first
output distribution is asserted; no unencoded physical universality is used. -/
theorem rangeTwo_encodedUniversality :
    ∃ C : ℕ, 0 < C ∧ ∀ F : SourceFamily, F.Effective →
      (∀ s, 0 < F.width s) →
      ∃ G : (s : Str) → List (ParityApp (4 * F.width s)),
        (ParityFamily.mk (fun s => 4 * F.width s) G).Effective ∧
        (∀ s g, g ∈ G s → g.Allowable) ∧
        (∀ s, RangeBound 2 (G s) ∧ (G s).length ≤ C * (F.gates s).length) ∧
        ∀ s (k : Fin (F.width s)), k.val = 0 →
          ∀ (q : Fin (4 * F.width s)), q.val = 0 →
            ∀ psi : EuclideanSpace ℂ (Qubits (F.width s)), IsState psi →
              ∀ b, singleWireProbability (parityCircuit (G s)).unitary
                  (encodeState encodeFourBits psi) q b =
                singleWireProbability (sourceCircuit (F.gates s)).unitary psi k b := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P77

end
