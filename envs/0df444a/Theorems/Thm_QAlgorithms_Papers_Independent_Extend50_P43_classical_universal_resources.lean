-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P43_classical_universal_resources
-- name    : QAlgorithms.Papers.Independent.Extend50.P43.classical_universal_resources
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:01:55.059+00:00
-- url     : https://prove2.me/theorems/e519a54c-a2dc-41a5-8430-19d676875314
-- title:
--   Classical truth-table programs and bounded-fan-in resource bounds
-- statement:
--   Let $m\geq1$. A classical programmable array is one fixed finite, well-formed circuit with $p$ program bits, $m$ data bits and $m$ fixed output wires. Each gate is an arbitrary Boolean function of finitely many earlier wires and produces one bit. Programs may depend on the selected function but not on its data input. There are exactly $2^{m2^m}$ functions $\{0,1\}^m\to\{0,1\}^m$, and a fixed universal array exists with $m2^m$ program bits. Moreover, for every $k\geq1$ and every such universal circuit with maximum fan-in at most $k$ and actual gate count $s$,
--
--   $$
--   p\geq m2^m,\qquad ks\geq m2^m.
--   $$
--
--   These bounds allow redundant supplied program bits and allow outputs to read input wires directly. They constrain the information that a universal circuit must use, rather than assuming every supplied program coordinate is effective. The gate inequality is expressed without truncated natural-number division.
-- source:
--   Programmable quantum gate arrays, arXiv:quant-ph/9703032v1, PDF p. 1, Unnumbered comparison: truth-table program length and classical bounded-fan-in gate lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P43

namespace QAlgorithms.Papers.Independent.Extend50.P43

open scoped ComplexConjugate

noncomputable section

/-- PDF p.1 and p.3: exactly 2^(m 2^m) classical m-bit functions exist,
m 2^m program bits suffice in one fixed circuit, and every universal circuit
with p program bits and maximum fan-in k has p >= m 2^m and
k times its actual gate count >= m 2^m. Redundant program bits and direct
input-to-output wires are allowed; universality supplies the necessary effective
program-bit dependence. Integer multiplication avoids truncated division. -/
theorem classical_universal_resources (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card (Qubits m → Qubits m) = 2 ^ (m * 2 ^ m) ∧
    (∃ circuit : ClassicalArray m (m * 2 ^ m), ClassicalUniversal circuit) ∧
    ∀ p k : ℕ, 1 ≤ k → ∀ circuit : ClassicalArray m p,
      HasFanInAtMost circuit k → ClassicalUniversal circuit →
        m * 2 ^ m ≤ p ∧ m * 2 ^ m ≤ k * circuit.gates.length := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P43
