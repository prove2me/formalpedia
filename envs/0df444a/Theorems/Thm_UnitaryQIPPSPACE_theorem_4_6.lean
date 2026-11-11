-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_theorem_4_6
-- name    : UnitaryQIPPSPACE.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:34:10.599891+00:00
-- url     : https://prove2.me/theorems/fbd253f4-6c4e-4594-a10c-e7de37255efb
-- title:
--   Theorem 4.6 — the unitary synthesis problem, positive answer [Ope26]
-- statement:
--   There is an algorithm that, on input $(1^n,1^t,1^\beta,d)$ with $n,\beta\ge1$, $t\ge0$ and $d\in[1,2^n]$ in binary, outputs a unitary oracle circuit $C_{n,d,t,\beta}$ of size $\mathrm{poly}(n+t+\beta)$ on registers $L$ ($t$ qubits), $Q$ ($n$ qubits) and an ancillary register, such that for every family of unitaries $\{U_\lambda\}_{\lambda\in\{0,1\}^t}$ on $\mathcal H_d=\operatorname{span}\{|0\rangle,\dots,|d-1\rangle\}$, with $U=\sum_\lambda|\lambda\rangle\langle\lambda|\otimes U_\lambda$ and $\iota:|\lambda\rangle|\psi\rangle\mapsto|\lambda\rangle|\psi\rangle|0\rangle$, there is a Boolean function $f_{U,\beta}$ with
--   $$\big\|C^{f_{U,\beta}}_{n,d,t,\beta}\,\iota-\iota\,U\big\|_{\mathrm{op}}\le2^{-\beta-1}.$$
--
--   Every unitary is implemented by a universal polynomial-size oracle circuit with a suitable Boolean oracle.
--
--   Differences from the source:
--   - reading: "There exists an algorithm" (no running time stated) → a machine that halts on every admissible input; no time bound; reason: none is stated in the theorem
--   - reading: the ancillary register is called A and E → one ancillary register; reason: a naming slip within the statement
--   - reading: f_{U,β} → f : {0,1}* → {0,1} may depend on U and on (n, d, t, β); reason: the circuit, hence its oracle, is fixed by (n, d, t, β)
--   - encoding: |j⟩ ∈ H_d → the n-qubit binary expansion of j, most significant qubit first; reason: the usual order of the computational basis
--   - encoding: the gate set G is fixed "without loss of generality, … for example, {H, T, CNOT}" → G = {H, T, CNOT} exactly; reason: the paper's own example; the classes do not depend on the choice of a finite universal gate set
--   - encoding: deterministic Turing machines → the published oracle Turing machines QAdvFew.PoQOracle.OTM run with the empty oracle; descriptions are tuple codes; reason: a standard machine model and a fixed injective code; polynomial time and space are preserved
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Theorem 4.6 ([Ope26, Theorem 1.1]), p.25 (PDF p.27)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_UnitaryQIPPSPACE_SpaceUniform
import Definitions.Def_UnitaryQIPPSPACE_OCirc
import Definitions.Def_AgnosticTNS_opNorm

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace UnitaryQIPPSPACE

/-- **Theorem 4.6 ([Ope26, Theorem 1.1])** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, p. 25 (PDF p. 27)): "There exists an algorithm
such that, on input `(1^n, 1^t, 1^β, d)` with integers `n, β ≥ 1`, `t ≥ 0`, and `d ∈ [1, 2^n]` encoded
in binary, outputs an oracle quantum circuit `C^{(·)}_{n,d,t,β}` of size `poly(n + t + β)` such that
• The circuit consists only of unitary gates and oracle queries.
• The workspace consists of a `t`-qubit register `L`, an `n`-qubit register `Q`, and an ancillary
register `A`.
Write `H_d := span{|0⟩, …, |d − 1⟩} ⊆ (ℂ²)^{⊗n}`. For every unitary family `{U_λ}_{λ ∈ {0,1}^t}`
acting on `H_d`, put `U := ∑_λ |λ⟩⟨λ| ⊗ U_λ`. Let `ι` be the isometry
`|λ⟩_L |ψ⟩_Q ↦ |λ⟩_L |ψ⟩_Q |0⟩_E` for `|ψ⟩ ∈ H_d`. Then there exists a Boolean function `f_{U,β}` such
that `‖C^{f_{U,β}}_{n,d,t,β} · ι − ι · U‖_op ≤ 2^{−β−1}`."

The algorithm is a machine `M` that halts on every admissible input `tup [1^n, 1^t, 1^β, bin(d)]` with
the description of `C_{n,d,t,β}` (a unitary oracle circuit on `t + n` data qubits, `L` first, then
`Q`, then its ancillas); its size is at most `P(n + t + β)` for one polynomial `P`. `U_λ` is a
`d × d` unitary and `ι` maps `ℂ^{2^t} ⊗ H_d` into the workspace (`|j⟩ ∈ H_d` is the binary expansion
of `j`, most significant qubit first). The norm is the operator norm on `L ⊗ H_d`.

**Formalization Note** The theorem states no running time for the algorithm, so none is imposed;
the ancillary register is called `A` and `E` in the same statement (one register). The Boolean
function `f_{U,β} : {0,1}* → {0,1}` may depend on `U` and on `(n, d, t, β)`. -/
theorem theorem_4_6 :
    ∃ (Cg : ℕ → ℕ → ℕ → ℕ → OCirc) (M : OTM) (P : Polynomial ℕ),
      ∀ n d t β : ℕ, 1 ≤ n → 1 ≤ β → 1 ≤ d → d ≤ 2 ^ n →
        (∃ T : ℕ, M.result noOracle (tup [unary n, unary t, unary β, natCode d]) T ≠ none ∧
          M.output noOracle (tup [unary n, unary t, unary β, natCode d]) T = (Cg n d t β).code) ∧
        (Cg n d t β).size ≤ P.eval (n + t + β) ∧ (Cg n d t β).Valid (t + n) ∧
        ∀ Ul : Bits t → Matrix.unitaryGroup (Fin d) ℂ, ∃ f : Str → Bool,
          AgnosticTNS.opNorm ((Cg n d t β).mat f (t + n + (Cg n d t β).anc) * iotaLd t n d (Cg n d t β).anc
            - iotaLd t n d (Cg n d t β).anc *
              (Matrix.of fun (x x' : Bits t × Fin d) => if x.1 = x'.1 then (Ul x.1 : Matrix (Fin d) (Fin d) ℂ) x.2 x'.2 else 0))
            ≤ (1 / 2 : ℝ) ^ (β + 1) := by sorry

end UnitaryQIPPSPACE
