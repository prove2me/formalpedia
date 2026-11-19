-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_actual_acceptance_polynomial
-- name    : QuantumBipartiteTesting.Bipartiteness.actual_acceptance_polynomial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:46:13.527273+00:00
-- url     : https://prove2.me/theorems/5b471a1c-6002-4a48-8e10-fa5680de82b9
-- title:
--   Acceptance polynomial of the actual finite quantum query circuit
-- statement:
--   Let $I$ be a finite address set and $S$ a finite non-null response alphabet. Fix an injective binary response encoding with zero-encoded null, a $q$-query quantum circuit with an input-independent unit start vector and input-independent complex unitaries, and a fixed Boolean computational-basis output event. The query adds the encoded response by XOR and acts as the identity on the finite workspace.
--
--   There is a real polynomial $P$ in the response indicators, of total degree at most $2q$, such that for every oracle $O:I\to S\cup\{\bot\}$,
--   $$
--   P\bigl((\mathbf1_{O(a)=z})_{(a,z)\in I\times S}\bigr)
--   =\Pr[A^O\text{ accepts}].
--   $$
--   The polynomial depends only on the circuit, encoding, and output event. All oracles, binary answer-register states, and finite workspaces remain included. This is the polynomial-existence step of Lemma 2.9; canonical response-table interpolation subsequently preserves its degree and values.
-- source:
--   Kayal, Sen, Szabó, Near-optimal quantum query lower bounds on bipartiteness and expansion testing in the bounded-degree graph model, held October 2026 manuscript, §2.4, Lemma 2.9, printed/PDF p. 10 (non-null response indicators and null elimination). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf The amplitude induction and sum-of-squares proof are Beals, Buhrman, Cleve, Mosca, de Wolf, Quantum Lower Bounds by Polynomials, Lemmas 4.1–4.2, printed p. 9 / PDF p. 9, https://homepages.cwi.nl/~rdewolf/publ/qc/polynomials.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Query
open QuantumBipartiteTesting.Bipartiteness

theorem QuantumBipartiteTesting.Bipartiteness.actual_acceptance_polynomial
    {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) :
    ∃ P : MvPolynomial (I × S) ℝ, P.totalDegree ≤ 2*q ∧
      ∀ O : I → Option S, MvPolynomial.eval (Indicators O) P = Accept E A out O := by sorry
