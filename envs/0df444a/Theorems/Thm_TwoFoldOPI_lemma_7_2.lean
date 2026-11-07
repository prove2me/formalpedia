-- Prove2me | Theorems.Thm_TwoFoldOPI_lemma_7_2
-- name    : TwoFoldOPI.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:49:12.186538+00:00
-- url     : https://prove2.me/theorems/8b067369-bb62-4cf2-aa04-29384c1658b5
-- title:
--   Lemma 7.2 — single-symbol unambiguous measurement
-- statement:
--   Let $\beta\in\mathbb F_q$ and $A_i=\mathbb F_q\setminus\{\beta\}$.
--   1. There is a measurement on one $\mathbb F_q$-qudit, with outcomes the unordered pairs of field elements, such that on input $X^c\mathrm{QFT}^\dagger|A_i\rangle$ (any $c\in\mathbb F_q$) it outputs $\{c,c'\}$ with $c'$ uniform on $\mathbb F_q\setminus\{c\}$.
--   2. It can be implemented to operator-norm error $\delta$ in time $\mathrm{poly}(q,\log(1/\delta))$: there are one uniform constructor and one polynomial $P$ such that, for every field, every $\beta$ and every $\delta>0$, on input $(F,\beta,\lceil\log_2(1/\delta)\rceil)$ the constructor outputs a gate-only program over $\{H,T,\mathrm{CNOT}\}$ on $N\ge2b$ wires whose circuit $U$ satisfies
--   $$\big\|U J_{\mathrm{in}}-J_{\mathrm{out}}V\big\|\le\delta ,$$
--   for an isometry $V$ from the qudit into ordered pairs whose induced unordered-pair measurement has the behaviour of 1. Here $J_{\mathrm{in}}$ places a symbol on the first $b$ wires and $J_{\mathrm{out}}$ an ordered pair on the first $2b$ wires, the other wires $|0\rangle$; the program's charged resources are at most $P(q+\lceil\log_2(1/\delta)\rceil)$.
--
--   Applied to every coordinate of the decoder input of Theorem 7.4, this measurement turns each symbol into an unordered pair that always contains the hidden symbol.
--
--   Differences from the source:
--   - reading: a quantum measurement … outputs the unordered pair {c, c′} for uniformly random c′ ← F_q∖{c} → a POVM indexed by Sym2 K with ⟨ϕ_c|E_s|ϕ_c⟩ = 1/(q − 1) when s = {c, c′}, c′ ≠ c, and 0 otherwise; reason: the outcome law of a measurement on a pure input is given by its POVM
--   - reading: it can be implemented to operator-norm error δ in time poly(q, log(1/δ)) → one uniform constructor (UniformResourceFamily) and one polynomial P; the constructed program is gate-only over {H, T, CNOT} with circuit U, ‖U J_in − J_out V‖ ≤ δ for an isometry V whose induced unordered-pair POVM satisfies clause 1; resources ≤ P(q + ⌈log₂(1/δ)⌉); reason: the proof implements an isometry followed by a standard-basis measurement (p.39); clean ancillas and a finite gate set are the p.26 conventions
--   - generalization: for one field F_q (time poly(q, log(1/δ))) → one constructor and one polynomial for every finite field, given as a presentation (p, f); reason: fixing the field gives the source's claim
--   - encoding: a single F_q-qudit, A_i for i ∈ [m] → a register of one symbol (Fin 1 → K); A_i = K ∖ {β} for an arbitrary β; reason: A_i depends on i only through β_i
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7.1, Lemma 7.2, p. 38

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Defs_OPIOraclePrograms
import Definitions.Def_QAlgorithms_Defs_OPIUniformity
import Definitions.Def_TwoFoldOPI_SymbolInput
import Definitions.Def_TwoFoldOPI_wordBits
import Definitions.Def_TwoFoldOPI_embedAt
import Definitions.Def_TwoFoldOPI_gateCircuit
import Definitions.Def_TwoFoldOPI_IsUnorderedPairPOVM
import Definitions.Def_TwoFoldOPI_inducedPOVM

open scoped Matrix

namespace TwoFoldOPI

open QAlgorithms QAlgorithms.OPI

/-- **Lemma 7.2 (single-symbol unambiguous measurement).**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7.1, Lemma 7.2, p.38: "Let A_i be as in Definition 7.1. For any i ∈ [m], there is a quantum
measurement on a single F_q-qudit with the following input-output behavior: when its input has the
form X^c QFT†|A_i⟩ for some c ∈ F_q, it outputs the unordered pair {c, c′} for uniformly random
c′ ← F_q∖{c}. Since it acts on one qudit of dimension q, it can be implemented to operator-norm
error δ in time poly(q, log(1/δ))."

1. For every finite field (presentation `F`) and every forbidden value `β` (`A_i = K ∖ {β}`)
   there is a POVM on one qudit with outcomes the unordered pairs that, on `X^c QFT†|A_i⟩`,
   outputs `{c, c′}` with `c′` uniform on `K ∖ {c}` (`IsUnorderedPairPOVM`).
2. There is one uniform constructor `A` and one polynomial `P` such that for every `F`, `β` and
   `δ > 0`, on input `(F, β, ⌈log₂(1/δ)⌉)` it outputs an oracle-free gate-only program over
   `{H, T, CNOT}` on `N ≥ 2b` wires (`b` bits per symbol), whose circuit `U` satisfies
   `‖U J_in − J_out V‖ ≤ δ` (operator norm) for an isometry `V : K → K × K` whose induced
   unordered-pair POVM is one as in 1; and the program's charged resources are at most
   `P(q + ⌈log₂(1/δ)⌉)`.

Here `J_in` places a symbol `y` on the first `b` wires and `J_out` an ordered pair `(a, a′)` on the
first `2b` wires (layout `wordBits`), all other wires `|0⟩`.

**Formalization Note.** "Implemented to operator-norm error δ" is read as: the circuit
approximates, on clean ancillas, an isometry whose standard-basis measurement followed by
forgetting the order is the measurement of clause 1. "In time poly(q, log(1/δ))" is one uniform
constructor (`QAlgorithms.OPI.UniformResourceFamily`, a public bit program whose own time and space
are polynomially bounded) and one polynomial `P` fixed before `F`, `β` and `δ`, bounding the
program's qubits, classical bits and gates (`membershipResources`). The gate set is
`{H, T, CNOT}`: nonexact gates are compiled (p.26). -/
theorem lemma_7_2 :
    (∀ (F : AvgCaseTI.FieldPres) (β : F.F), ∃ E, IsUnorderedPairPOVM F β E) ∧
    ∃ (A : UniformResourceFamily SymbolInput SymbolInput.encode SymbolInput.scale)
      (P : Polynomial ℕ),
      ∀ (F : AvgCaseTI.FieldPres) (β : F.F) (δ : ℝ), 0 < δ →
        let x : SymbolInput := ⟨F, β, ⌈Real.logb 2 (1 / δ)⌉₊⟩
        (A.construct x).oracles = 0 ∧
        2 * bitsPerSymbol F ≤ (A.construct x).qubits ∧
        membershipResources (A.construct x).program (fun _ => 1) ≤ P.eval x.scale ∧
        ∃ U : Circuit htcxGateSet (A.construct x).qubits,
          gateCircuit (A.construct x).program = some U ∧
          ∃ V : Matrix (F.F × F.F) (Fin 1 → F.F) ℂ,
            Vᴴ * V = 1 ∧ IsUnorderedPairPOVM F β (inducedPOVM V) ∧
            specNorm (U.unitary *
                (Matrix.of fun (z : Qubits (A.construct x).qubits) (y : Fin 1 → F.F) =>
                  if z = embedAt (A.construct x).qubits (wordBits F 1 y) then (1 : ℂ) else 0) -
              (Matrix.of fun (z : Qubits (A.construct x).qubits) (ab : F.F × F.F) =>
                  if z = embedAt (A.construct x).qubits (wordBits F 2 ![ab.1, ab.2])
                  then (1 : ℂ) else 0) * V) ≤ δ := by sorry

end TwoFoldOPI
