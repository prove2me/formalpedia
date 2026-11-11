-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_lemma_4_7
-- name    : UnitaryQIPPSPACE.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:20.772978+00:00
-- url     : https://prove2.me/theorems/94b9e10c-9202-459b-ad50-54b7e01264af
-- title:
--   Lemma 4.7 — effective synthesis from PSPACE-computable entries
-- statement:
--   Let $\{W_n\}$ be a unitary family with PSPACE-computable entries, $W_n$ on $n$ qubits. Then there are a language $A_W\in\mathsf{PSPACE}$ and a deterministic polynomial-time algorithm that, on input $(1^n,1^\beta)$ with $n,\beta\ge1$, outputs a unitary oracle circuit $C_{n,\beta}$ of size $\mathrm{poly}(n,\beta)$, consisting only of gates and oracle queries, on an $n$-qubit register $Q$ and an ancillary register $E$, such that
--   $$\big\|C^{A_W}_{n,\beta}\iota-\iota W_n\big\|_{\mathrm{op}}\le2^{-\beta-1},\qquad\iota:|\psi\rangle_Q\mapsto|\psi\rangle_Q|0\rangle_E.$$
--
--   This is a PSPACE-effective form of unitary synthesis: a single PSPACE oracle suffices for every family with PSPACE-computable entries.
--
--   Differences from the source:
--   - encoding: size poly(n, β) → size at most P(n + β) for one polynomial P; reason: equivalent
--   - encoding: an oracle quantum circuit consisting only of unitary gates and oracle queries → a list of {H, T, CNOT} gates and queries O_A on named qubits, with an ancilla count; reason: the paper's model with the fixed gate set
--   - encoding: deterministic Turing machines → the published oracle Turing machines QAdvFew.PoQOracle.OTM run with the empty oracle; descriptions are tuple codes; reason: a standard machine model and a fixed injective code; polynomial time and space are preserved
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Lemma 4.7, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_PSPACE
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_UnitaryQIPPSPACE_PSPACEComputableFam
import Definitions.Def_UnitaryQIPPSPACE_OCirc
import Definitions.Def_AgnosticTNS_opNorm

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace UnitaryQIPPSPACE

/-- **Lemma 4.7 (Effective synthesis from PSPACE-computable entries)** (He, Ou, Zhao, *unitaryQIP =
unitaryPSPACE*, arXiv:2611.02819, held version sha256 9e357a00…, p. 25 (PDF p. 27)): "Let
`W = {W_n}` be a unitary family with PSPACE-computable entries, where each `W_n` acts on `n` qubits.
Then there exists a language `A_W ∈ PSPACE` and a deterministic polynomial-time algorithm that, on
input `(1^n, 1^β)` with integers `n, β ≥ 1`, outputs an oracle quantum circuit `C^{(·)}_{n,β}` of size
`poly(n, β)` such that
• The circuit `C^{(·)}_{n,β}` consists only of unitary gates and oracle queries.
• The workspace of `C^{(·)}_{n,β}` consists of an `n`-qubit register `Q` and an ancillary register `E`.
Let `ι` be the isometry `|ψ⟩_Q ↦ |ψ⟩_Q |0⟩_E`. Then `‖C^{A_W}_{n,β} · ι − ι · W_n‖_op ≤ 2^{−β−1}`."

The algorithm is a machine `M` with a polynomial time bound `p`: on `tup [1^n, 1^β]` it has halted
after `p(n + β)` steps with the description of `C_{n,β}` (a unitary oracle circuit, `OCirc`, whose
data register is `Q` and whose ancillas are `E`); the size is at most `P(n + β)`.

**Formalization Note** `PSPACE` is the published `QAdvFew.PoQOracle.PSPACE` with the empty oracle;
the oracle `A_W` acts on a query `|x, b⟩` as `|x, b ⊕ A_W(x)⟩`, `x` the string on the query's input
qubits. -/
theorem lemma_4_7 (W : (n : ℕ) → Matrix (Bits n) (Bits n) ℂ)
    (hU : ∀ n, W n ∈ Matrix.unitaryGroup (Bits n) ℂ) (hW : HasPSPACEEntries W) :
    ∃ A : Set Str, A ∈ PSPACE noOracle ∧
      ∃ (Cg : ℕ → ℕ → OCirc) (M : OTM) (p P : Polynomial ℕ), ∀ n β : ℕ, 1 ≤ n → 1 ≤ β →
        M.result noOracle (tup [unary n, unary β]) (p.eval (n + β)) ≠ none ∧
        M.output noOracle (tup [unary n, unary β]) (p.eval (n + β)) = (Cg n β).code ∧
        (Cg n β).size ≤ P.eval (n + β) ∧ (Cg n β).Valid n ∧
        AgnosticTNS.opNorm ((Cg n β).mat (langOracle A) (n + (Cg n β).anc) * iota n (Cg n β).anc
          - iota n (Cg n β).anc * W n) ≤ (1 / 2 : ℝ) ^ (β + 1) := by sorry

end UnitaryQIPPSPACE
