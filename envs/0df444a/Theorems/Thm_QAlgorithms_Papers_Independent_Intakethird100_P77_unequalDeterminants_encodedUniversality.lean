-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P77_unequalDeterminants_encodedUniversality
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P77.unequalDeterminants_encodedUniversality
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:10:20.165699+00:00
-- url     : https://prove2.me/theorems/c7f2f05e-e251-4b6f-9a70-248be4ca9d60
-- title:
--   Nearest-neighbour parity gates without the determinant constraint are efficiently universal
-- statement:
--   Consider the same effective nearest-neighbour controlled-$Z$/one-qubit source presentation with a first-wire output. If a parity-preserving gate may use arbitrary unitary even and odd blocks, without requiring their determinants to agree, there is an absolute $C>0$ and an effective target family on four wires per logical wire satisfying
--
--   $$|G_s|\le C|C_s|,\qquad \operatorname{range}(G_s)\le1,\qquad p_b(G_s,E_4\psi,1)=p_b(C_s,\psi,1).$$
--
--   The encoder $E_4$ sends logical basis states to $0000$ and $1001$ and is extended linearly; the equality holds for every normalized logical input $\psi$ and either outcome $b$. All blocks remain unitary. This specifies the encoded input/output meaning of efficient universality after dropping the determinant constraint.
-- source:
--   Matchgates and classical simulation of quantum circuits, arXiv:0804.4050v2, PDF p. 4, Section 2: nearest-neighbour parity-preserving gates without determinant constraint are universal

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P77

open QAlgorithms

open QAlgorithms.Complexity (Str)

open QAlgorithms.Papers.Independent.Advance50.P19 (Major CARSystem)

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4: dropping only det A=det B permits physical SWAP and gives a
uniform encoded nearest-neighbour simulation, preserving the first output
probability. A and B remain unitary. The source size convention is as in
Theorem 2, rather than arbitrary-connectivity routing at constant cost. -/
theorem unequalDeterminants_encodedUniversality :
    ∃ C : ℕ, 0 < C ∧ ∀ F : SourceFamily, F.Effective →
      (∀ s, 0 < F.width s) →
      ∃ G : (s : Str) → List (ParityApp (4 * F.width s)),
        (ParityFamily.mk (fun s => 4 * F.width s) G).Effective ∧
        (∀ s, RangeBound 1 (G s) ∧ (G s).length ≤ C * (F.gates s).length) ∧
        ∀ s (k : Fin (F.width s)), k.val = 0 →
          ∀ (q : Fin (4 * F.width s)), q.val = 0 →
            ∀ psi : EuclideanSpace ℂ (Qubits (F.width s)), IsState psi →
              ∀ b, singleWireProbability (parityCircuit (G s)).unitary
                  (encodeState encodeFourBits psi) q b =
                singleWireProbability (sourceCircuit (F.gates s)).unitary psi k b := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P77

end
