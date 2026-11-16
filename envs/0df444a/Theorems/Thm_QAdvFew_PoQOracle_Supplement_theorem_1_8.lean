-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_Supplement_theorem_1_8
-- name    : QAdvFew.PoQOracle.Supplement.theorem_1_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:22:50.917201+00:00
-- url     : https://prove2.me/theorems/1c94ab7b-854b-4c76-b914-ba9caaaedb7a
-- title:
--   Theorem 1.8 — a quantum oracle with $\mathsf{BQP}=\mathsf{QCMA}$ and four-message qv-OSP
-- statement:
--   There exists a quantum oracle $O$, that is, a family of unitary operators, relative to which
--
--   1. $\mathsf{BQP}^O=\mathsf{QCMA}^O$, and
--   2. a four-message quantum-verifier oblivious state preparation protocol (qv-OSP) exists.
--
--   Together with the implications from qv-OSP to QCCC commitments and key exchange, this shows that even qv-OSP gives no relativizing construction of efficiently verifiable one-way puzzles, whose existence implies $\mathsf{BQP}\neq\mathsf{QCMA}$ (Corollary 1.9).
--
--   **Formalization Note** The oracle is a single unitary oracle with an arbitrary arity; a classical oracle such as PSPACE can be one of its components through $|x,z\rangle\mapsto|x,z\oplus f(x)\rangle$. The classical-oracle slot of the classes is the constant-$0$ oracle.
--
--   Differences from the source:
--   - encoding: a quantum oracle (a family of unitary operators) → an arity ar and a matrix family O : UOracle ar with O.IsUnitary; reason: Lean representation of a family of unitaries indexed by component and level
--   - encoding: QPT/nonuniform QPT algorithms and parties with oracle access, as in §3.2.1–§3.2.2 → uniform (resp. arbitrary) polynomially bounded families of Clifford+T circuits with classical-oracle gates and controlled/inverse unitary-oracle gates; size = binary description length plus t per level-t query; component/level superposition via controlled queries; reason: Lean representation of the paper's conventions; polynomially equivalent
--   - encoding: probabilities over the parties' randomness and measurements in a protocol with classical communication → sum over transcripts of the product of the two parties' likelihoods; messages of one fixed polynomial length (zero-padded); reason: the standard decomposition for classical communication; a polynomial-time party reads polynomially many bits
--   - reading: a four message qv-OSP → a qv-OSP protocol with exactly four alternating classical messages at every n, either party sending first; reason: the paper does not say which party sends first; both are allowed
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Theorem 1.8, pp. 3–4 (PDF pp. 5–6)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Supplement_BQPU
import Definitions.Def_QAdvFew_PoQOracle_Supplement_QCMAU
import Definitions.Def_QAdvFew_PoQOracle_Supplement_IsQvOSP

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle.Supplement

/-- **Theorem 1.8** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Theorem 1.8, pp. 3–4 (PDF pp. 5–6)): "There exists a quantum oracle relative
to which 1. `BQP = QCMA` 2. a four message qv-OSP exists."

There are an arity `ar` and a unitary oracle `O` (a single family of unitaries, §3.2.2) such that
`BQP^O = QCMA^O` and some protocol with exactly four classical messages is a qv-OSP relative to
`O`.

**Formalization Note** "Relative to `O`" alone: the classical oracle slot is the constant-`false`
oracle, whose gates do nothing. A classical oracle such as PSPACE can be one component of `O`,
through `|x, z⟩ ↦ |x, z ⊕ f(x)⟩` ("Classical oracles are included as a special case", §3.2.3). -/
theorem theorem_1_8 :
    ∃ (ar : ℕ → ℕ → ℕ) (O : UOracle ar), O.IsUnitary ∧
      BQPU O (fun _ => false) = QCMAU O (fun _ => false) ∧
      ∃ (Pr : QVProtocol ar) (P : IParty ar (fun n => Pr.ℓ.eval n)),
        IsQvOSP O (fun _ => false) Pr P ∧ FourMessage Pr := by sorry

end QAdvFew.PoQOracle.Supplement
