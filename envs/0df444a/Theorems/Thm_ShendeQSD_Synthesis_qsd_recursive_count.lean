-- Prove2me | Theorems.Thm_ShendeQSD_Synthesis_qsd_recursive_count
-- name    : ShendeQSD.Synthesis.qsd_recursive_count
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:38.474113+00:00
-- url     : https://prove2.me/theorems/c7a78f88-c3b7-4bf3-b607-3a29ca46924f
-- title:
--   Eq. (18): CNOT count of the recursive Quantum Shannon Decomposition
-- statement:
--   Let $1\le\ell\le n$ and $c\in\mathbb N$. Suppose every unitary on $\ell$ qubits is implemented exactly by a circuit of one-qubit gates and CNOTs with at most $c$ CNOTs. Then every unitary on $n$ qubits is implemented exactly by such a circuit with at most
--
--   $$
--   4^{n-\ell}\big(c+3\cdot2^{\ell-1}\big)-3\cdot2^{n-1}
--   $$
--
--   CNOTs.
--
--   This is the count of the Quantum Shannon Decomposition applied recursively down to $\ell$-qubit operators. With $\ell=1$, $c=0$ it gives $\tfrac34 4^n-\tfrac32 2^n$; with $\ell=2$, $c=3$ it gives $\tfrac9{16}4^n-\tfrac32 2^n$ (Table 1).
--
--   **Formalization Note** The bound is compared in $\mathbb R$; the exponents $n-\ell$, $\ell-1$, $n-1$ are natural numbers and exact under $1\le\ell\le n$.
--
--   Differences from the source:
--   - reading: c_n, the least number of CNOTs needed by some known synthesis algorithm (p. 14) → the existence of a circuit over the gate library implementing U with at most that many CNOTs; reason: the inequality is a statement about circuits the algorithm produces
--   - encoding: implementing an operator → circuit operator equal to U, no global phase, no ancilla; reason: one-qubit gates range over all of U(2), and the paper's circuits use no ancilla
--   - reading: ℓ-qubit operators with ℓ ≤ n → 1 ≤ ℓ ≤ n; reason: the recursion bottoms out at one- or two-qubit operators and never goes below one qubit
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, §5.3, Eq. (18), p. 14

import Definitions.Def_ShendeQSD_Synthesis_cnotCount

namespace ShendeQSD.Synthesis

open QAlgorithms

/-- **Eq. (18): the CNOT count of the recursive Quantum Shannon Decomposition.**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
§5.3, Eq. (18), p. 14: "If ℓ-qubit operators may be implemented using ≤ c_ℓ CNOT gates, one can
prove the following inequality for c_n by induction. c_n ≤ 4^{n−ℓ}(c_ℓ + 3 × 2^{ℓ−1}) − 3 × 2^{n−1}".

For `1 ≤ ℓ ≤ n` and `c ∈ ℕ`: if every unitary on `ℓ` qubits is implemented exactly by a circuit
of one-qubit gates and CNOTs with at most `c` CNOTs, then every unitary `U` on `n` qubits is
implemented exactly by such a circuit with at most `4^{n−ℓ}(c + 3·2^{ℓ−1}) − 3·2^{n−1}` CNOTs.

**Formalization Note.** Reading: `c_n ≤ …` is read as the existence of a circuit over the gate
library implementing `U` exactly (no global phase, no ancilla) with that many CNOTs. The count is
compared in `ℝ`; the natural-number subtractions in the exponents are exact since `1 ≤ ℓ ≤ n`. -/
theorem qsd_recursive_count (ℓ n c : ℕ) (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n)
    (hc : ∀ V ∈ Matrix.unitaryGroup (Qubits ℓ) ℂ,
      ∃ c' : Circuit gateLib ℓ, c'.unitary = V ∧ cnotCount c' ≤ c) :
    ∀ U ∈ Matrix.unitaryGroup (Qubits n) ℂ, ∃ c' : Circuit gateLib n, c'.unitary = U ∧
      (cnotCount c' : ℝ) ≤ (4 : ℝ) ^ (n - ℓ) * ((c : ℝ) + 3 * 2 ^ (ℓ - 1)) - 3 * 2 ^ (n - 1) := by sorry

end ShendeQSD.Synthesis
