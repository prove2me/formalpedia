-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P77_pairEncoding_rangeThree
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P77.pairEncoding_rangeThree
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:11:09.169201+00:00
-- url     : https://prove2.me/theorems/e815f9ef-c1ac-4d42-8ea2-256c1a483942
-- title:
--   Pair encoding yields a range-three simulation
-- statement:
--   Let $C_s$ be an effectively uniform circuit family in nearest-neighbour controlled-$Z$/one-qubit normal form, with positive logical width and first-wire output. Encode $|0\rangle$ as $|00\rangle$ and $|1\rangle$ as $|11\rangle$, extending the encoding $E_2$ linearly. A target family of allowable matchgates on two physical wires per logical wire can be fixed before the quantum input so that, for an absolute $C>0$,
--
--   $$|G_s|\le C|C_s|,\qquad \operatorname{range}(G_s)\le3,\qquad p_b(G_s,E_2\psi,1)=p_b(C_s,\psi,1).$$
--
--   The probability equality holds for every normalized logical input $\psi$ and both output values $b$. Effective descriptions of target structure and gate entries are included. This is an upper bound from the alternative construction; it asserts no minimality of range three.
-- source:
--   Matchgates and classical simulation of quantum circuits, arXiv:0804.4050v2, PDF p. 6, Section 2 closing remark: pair encoding gives range three

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P77

open QAlgorithms

open QAlgorithms.Complexity (Str)

open QAlgorithms.Papers.Independent.Advance50.P19 (Major CARSystem)

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6 closing remark: the alternative two-wire encoding admits a uniform
range-three upper bound and constant gate overhead. No minimality of range
three is asserted. The first physical line is the logical output line. -/
theorem pairEncoding_rangeThree :
    ∃ C : ℕ, 0 < C ∧ ∀ F : SourceFamily, F.Effective →
      (∀ s, 0 < F.width s) →
      ∃ G : (s : Str) → List (ParityApp (2 * F.width s)),
        (ParityFamily.mk (fun s => 2 * F.width s) G).Effective ∧
        (∀ s g, g ∈ G s → g.Allowable) ∧
        (∀ s, RangeBound 3 (G s) ∧ (G s).length ≤ C * (F.gates s).length) ∧
        ∀ s (k : Fin (F.width s)), k.val = 0 →
          ∀ (q : Fin (2 * F.width s)), q.val = 0 →
            ∀ psi : EuclideanSpace ℂ (Qubits (F.width s)), IsState psi →
              ∀ b, singleWireProbability (parityCircuit (G s)).unitary
                  (encodeState encodeTwoBits psi) q b =
                singleWireProbability (sourceCircuit (F.gates s)).unitary psi k b := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P77

end
