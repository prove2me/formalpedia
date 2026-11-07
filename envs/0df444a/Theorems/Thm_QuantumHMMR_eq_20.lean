-- Prove2me | Theorems.Thm_QuantumHMMR_eq_20
-- name    : QuantumHMMR.eq_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:52.796951+00:00
-- url     : https://prove2.me/theorems/f3abb50f-5dd9-415b-9a47-4165df7e82eb
-- title:
--   Eq. (20) — $\dim S(U|0^n\rangle) \ge n - h$ after at most $h$ rotations
-- statement:
--   1. $\dim S(|0^n\rangle) = n$.
--   2. A Clifford unitary $C$ preserves the stabilizer dimension: $\dim S(C\psi) = \dim S(\psi)$.
--   3. At a single-qubit $Z$ rotation $e^{i\varphi Z_i}$ on qubit $i$, the stabilizers commuting with $Z_i$ remain stabilizers, and commutation with $Z_i$ is at most one binary linear constraint on the labels: $\dim S(e^{i\varphi Z_i}\psi) \ge \dim S(\psi) - 1$.
--   4. For $n \ge 2$, a two-qubit Clifford gate placed on a ring edge is an $n$-qubit Clifford unitary.
--   5. Hence, for $n \ge 2$, if a word of walk updates (two-qubit Clifford gates on ring edges and rotations $e^{i\varphi Z}$ on the first qubit) contains at most $h$ rotations, its product $U$ satisfies
--   $$
--   \dim S(U|0^n\rangle) \ge n - h. \tag{20}
--   $$
--
--   With $h = 2T/m = 6\lceil\log^2 n\rceil$ this is applied outside the event of Eq. (19).
--
--   Differences from the source:
--   - generalization: a Clifford step of the walk (a gate of G on a ring edge) → every n-qubit Clifford unitary, acting on every vector ψ; reason: edge gates of G are Clifford unitaries (clause 4)
--   - generalization: a Z rotation inserted in the walk → a Z rotation on any wire i, any angle, any vector ψ; reason: the walk's insertions are rotations on wire 0
--   - generalization: the walk's local gates are drawn from G → the word clause allows any two-qubit Clifford on a ring edge; reason: G ⊆ C₂
--   - reading: "a Clifford step" (that a local Clifford gate on the ring is an n-qubit Clifford is implicit) → explicit clause 4 for n ≥ 2; reason: the page uses it to apply clause 2 to the walk
--   - reading: "outside this event there are at most h non-Clifford gates … gives dim S(U|0ⁿ⟩) ≥ n − h" → a deterministic statement about every word of updates with at most h rotations, n ≥ 2; reason: the probabilistic event enters only through the count of rotations; n ≥ 2 is the ring of the walk
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), proof of Theorem 1.3, Eq. (20), p.16

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_ProjectiveCliffords
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
import Definitions.Def_QuantumHMMR_rotZ
import Definitions.Def_QuantumHMMR_stabDim

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45

namespace QuantumHMMR

/-- **Eq. (20)** (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), proof of Theorem 1.3, p.16). `dim S(|0ⁿ⟩) = n`; a Clifford gate preserves
`dim S`; at a single-qubit `Z`-rotation gate on qubit `i` the stabilizers commuting with `Z_i` remain
stabilizers, and commutation with `Z_i` is at most one binary linear constraint, so `dim S` drops by
at most one. Hence, if a word of walk updates contains at most `h` single-qubit non-Clifford gates,
`dim S(U|0ⁿ⟩) ≥ n - h` for its product `U`.

The clauses: (1) `dim S(|0ⁿ⟩) = n`; (2) every Clifford `C` (unitary normalizer of the Pauli group)
satisfies `dim S(Cψ) = dim S(ψ)`; (3) `dim S(ψ) ≤ dim S(e^{iφZ_i} ψ) + 1` for every wire `i`, angle
`φ` and vector `ψ`; (4) for `n ≥ 2`, a two-qubit Clifford placed on a ring edge is an `n`-qubit
Clifford; (5) for `n ≥ 2`, every word of updates (local Clifford gates on ring edges, `e^{iφZ}` on the
first qubit) with at most `h` rotations gives `dim S(U|0ⁿ⟩) ≥ n - h`.

**Formalization Note** A word is a list, first update first; an entry is either `(i, C)` (the
two-qubit Clifford `C` on edge `(i, i + 1)`, published `edgeLift`) or an angle `φ` (published
`firstWireLift` of `e^{iφZ}`); its product is `U_r ⋯ U_1`. Words, not probabilities: (5) is the
deterministic step behind (20). `n ≥ 2` is the ring the walk lives on. -/
theorem eq_20 (n : ℕ) :
    stabDim (zeroKet n) = n ∧
    (∀ C ∈ Clifford.normalizer n, ∀ ψ : EuclideanSpace ℂ (Qubits n),
      stabDim (act (C : QMat n) ψ) = stabDim ψ) ∧
    (∀ (i : Fin n) (φ : ℝ) (ψ : EuclideanSpace ℂ (Qubits n)),
      stabDim ψ ≤ stabDim (act (embedOp (k := 1) (rotZ φ)
        ⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩) ψ) + 1) ∧
    (2 ≤ n → ∀ (i : Fin n) (C : Clifford.normalizer 2),
      ∃ V ∈ Clifford.normalizer n, (V : QMat n) = edgeLift i C.val.val) ∧
    (2 ≤ n → ∀ (h : ℕ) (w : List ((Fin n × Clifford.normalizer 2) ⊕ ℝ)),
      (w.filter Sum.isRight).length ≤ h →
      n - h ≤ stabDim (act ((w.map fun u => Sum.elim (fun e => edgeLift e.1 e.2.val.val)
        (fun φ => firstWireLift n (rotZ φ)) u).reverse.prod) (zeroKet n))) := by sorry

end QuantumHMMR
