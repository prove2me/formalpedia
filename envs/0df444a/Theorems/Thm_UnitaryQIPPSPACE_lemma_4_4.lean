-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_lemma_4_4
-- name    : UnitaryQIPPSPACE.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:12.316195+00:00
-- url     : https://prove2.me/theorems/e61eb93a-1d76-4c49-a334-dd46e785a36d
-- title:
--   Lemma 4.4 — entries of a space-uniform channel are PSPACE-computable
-- statement:
--   Let $\{C_n\}$ be a space-uniform circuit family, each $C_n$ with $n$ input and $n$ output qubits. Then the numbers
--   $$\langle i|C_n(|x\rangle\langle y|)|j\rangle,\qquad i,j,x,y\in\{0,1\}^n,$$
--   have modulus at most $1$, and the family indexed by $(1^n,i,j,x,y)$ is PSPACE-computable.
--
--   It is the computability input of Proposition 4.5.
--
--   Differences from the source:
--   - encoding: the index (1^n, i, j, x, y) → tup [1^n, i, j, x, y] with bit strings; reason: a fixed self-delimiting code
--   - encoding: the gate set G is fixed "without loss of generality, … for example, {H, T, CNOT}" → G = {H, T, CNOT} exactly; reason: the paper's own example; the classes do not depend on the choice of a finite universal gate set
--   - encoding: deterministic Turing machines → the published oracle Turing machines QAdvFew.PoQOracle.OTM run with the empty oracle; descriptions are tuple codes; reason: a standard machine model and a fixed injective code; polynomial time and space are preserved
--   - reading: space-uniform: a polynomial-space machine "on input (1^n, i), outputs the i-th operation of C_n" → for every i ≤ |C_n| the machine on (1^n, bin i) uses at most p(n) cells and outputs the i-th operation, or the empty string at i = |C_n|; reason: the end marker makes the machine determine the circuit (the standard reading of [MY23]); it bounds |C_n| by 2^{O(p(n))}
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Lemma 4.4 ([MY23, Lemma 6.2], extended), p.22 (PDF p.24)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_UnitaryQIPPSPACE_SpaceUniform
import Definitions.Def_UnitaryQIPPSPACE_PSPACEComputableFam

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace UnitaryQIPPSPACE

/-- **Lemma 4.4 (Computability of entries of a space-uniform channel, [MY23, Lemma 6.2], extended)**
(He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*, arXiv:2611.02819, held version sha256 9e357a00…, p. 22
(PDF p. 24)): "Let `{C_n}` be space-uniform, each with `n` input qubits and `n` output qubits. Then,
we have that the family `{⟨i|C_n(|x⟩⟨y|)|j⟩}_{(1^n, i, j, x, y)}` consists of numbers of modulus at most
1 and is PSPACE-computable."

**Formalization Note** The index `(1^n, i, j, x, y)` is encoded as `tup [1^n, i, j, x, y]` with
`i, j, x, y ∈ {0,1}^n` written as bit strings; `⟨i|X|j⟩` is the entry `X i j`. -/
theorem lemma_4_4 (C : ℕ → Circuit) (hSU : SpaceUniform C id) (hWF : ∀ n, (C n).WF n n) :
    (∀ (n : ℕ) (i j x y : Bits n), ‖(C n).chan n n (Matrix.single x y 1) i j‖ ≤ 1) ∧
    PSPACEComputableFam (J := Σ n : ℕ, Bits n × Bits n × Bits n × Bits n)
      (fun e => tup [unary e.1, e.2.1.toStr, e.2.2.1.toStr, e.2.2.2.1.toStr, e.2.2.2.2.toStr])
      (fun e => (C e.1).chan e.1 e.1 (Matrix.single e.2.2.2.1 e.2.2.2.2 1) e.2.1 e.2.2.1) := by sorry

end UnitaryQIPPSPACE
