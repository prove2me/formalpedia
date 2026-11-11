-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_7_4
-- name    : QuantumXoP.Security.lemma_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:07:06.794165+00:00
-- url     : https://prove2.me/theorems/c6f207f2-3a79-47f9-8a04-e7e39e3caa15
-- title:
--   Lemma 7.4 — expected numbers of queried inputs and collisions in the compressed database
-- statement:
--   Let $|\Xi_t\rangle$ be the final joint algorithm–database state of an algorithm that starts from $|\mathrm{start}\rangle\otimes|\emptyset\rangle$ with $\|\mathrm{start}\|\le1$, applies arbitrary contractions (for example unitaries or orthogonal projections) to its own registers, and makes $t\le N$ queries to the compressed oracle $O$ in between. Then
--   $$\langle\Xi_t|D_{\mathrm{cnt}}|\Xi_t\rangle\le t,\qquad\langle\Xi_t|\mathrm{Col}_{\mathrm{cnt}}|\Xi_t\rangle\le129\,t.$$
--
--   With Eq. (36) it bounds each term of the commutator expansion (34) in the proof of Lemma 7.2.
--
--   **Formalization Note** The algorithm registers are query input, query answer and an arbitrary finite workspace. Between consecutive queries a single contraction is applied; a product of contractions is a contraction.
--
--   Differences from the source:
--   - generalization: "some algorithm": oracle-independent unitaries on the algorithm registers starting from a unit state, and in its use on p. 39 the component of such a run on an auxiliary qubit (an orthogonal projection, unnormalized) → any start state of norm at most 1 and arbitrary contractions on the algorithm registers between the queries; reason: unitaries and orthogonal projections are contractions and a unit state has norm 1, so the statement specializes to every case the paper uses; App. C, p. 47, argues projections explicitly
--   - generalization: n is a fixed positive integer (§2, p. 8) → every n : ℕ, including n = 0; reason: the case n = 0 is one extra instance; the statement specializes to every n ≥ 1
--   - encoding: the usual query on a database register → the identity when the register is |⊥⟩; reason: the queried register has no |⊥⟩ component on states reached from |∅⟩, so this convention is never used
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 37 (PDF p. 39), Lemma 7.4 (proof App. C, pp. 45–47; its use on p. 39)

import Mathlib
import Definitions.Def_QuantumXoP_Security_Compressed

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 7.4 (p. 37; proof App. C): let `|Ξ_t⟩` be the joint algorithm–database state after an
algorithm that starts from `|start⟩ ⊗ |∅⟩` with `‖start‖ ≤ 1`, interleaves arbitrary contractions
of its own registers (unitaries, orthogonal projections) with `t ≤ N` compressed queries. Then
`⟨Ξ_t| D_cnt |Ξ_t⟩ ≤ t` and `⟨Ξ_t| Col_cnt |Ξ_t⟩ ≤ 129 t`. -/
theorem lemma_7_4 {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {t : ℕ}
    (start : EuclideanSpace ℂ (Reg n W)) (hstart : ‖start‖ ≤ 1)
    (V : Fin (t + 1) → Matrix (Reg n W) (Reg n W) ℂ) (hV : ∀ i, IsContraction (V i))
    (ht : t ≤ 2 ^ n) :
    expectDiag (compExec start V) dcnt ≤ t ∧
      expectDiag (compExec start V) colcnt ≤ 129 * t := by sorry

end QuantumXoP.Security
