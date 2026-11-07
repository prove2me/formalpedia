-- Prove2me | Theorems.Thm_QuarticGap_lemma_2_8
-- name    : QuarticGap.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:00.982203+00:00
-- url     : https://prove2.me/theorems/9dcf6da0-178b-49c0-9896-98c041448271
-- title:
--   Lemma 2.8 — amplitude amplification with an unknown success probability and a known lower bound $p_0$
-- statement:
--   Let $V$ be a quantum circuit that makes $r$ queries, let $\Pi$ be an orthogonal projection that does not depend on the input, and suppose $p = \|\Pi V|0\rangle\|^2 \ge p_0$ for a known $p_0 \in (0,1]$. For every $\varepsilon \in (0,1)$ there is a quantum algorithm that makes
--   $$
--   O\Bigl(\frac{r(1+\log(1/\varepsilon))}{\sqrt{p_0}}\Bigr)
--   $$
--   queries and, with probability at least $1-\varepsilon$, outputs the state $\Pi V|0\rangle/\sqrt p$; otherwise it reports failure.
--
--   This turns the state preparation with squared norm at least $1/(16n)$ into a sampler with $O(\sqrt n)$ queries.
--
--   **Formalization Note** The algorithm is one circuit $U$, fixed before the oracles, with $N$ output wires, a flag wire and $t$ work wires. The part of its final state with the flag up is $(\Pi V|0\rangle/\sqrt p) \otimes g$ with $\|g\|^2 \ge 1-\varepsilon$, and the flag down is failure. The $O(\cdot)$ constant is absolute.
--
--   Differences from the source:
--   - reading: a quantum algorithm with intermediate measurements that outputs a state or reports failure → one unitary oracle circuit with a flag wire, in which the flagged part of the final state is the target tensored with a vector g of squared norm at least 1 − ε; reason: measurements can be deferred, and controlled queries are available; the global sign of the source proof is absorbed by g
--   - encoding: a circuit V on an input, and an orthogonal projection Π; V makes r queries → V run on any tuple of unitary oracles orc; Π a Hermitian idempotent matrix P; r the total query count of V; reason: the queries of a quantum circuit are unitaries, and Hermitian idempotents are the orthogonal projections
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Lemma 2.8, p.19

import Mathlib
import Definitions.Def_QuarticGap_IsCoherentAccess

open QAlgorithms

namespace QuarticGap

/-- Lemma 2.8 (arXiv:2610.42069 (file sha256 9f68aaf9…), p.19), amplitude amplification with an
unknown success probability and a known lower bound. Let `V` be a circuit with `r` queries, `Π` an
orthogonal projection independent of the input, and `p = ∥ΠV|0⟩∥² ≥ p₀`. For every `ε ∈ (0, 1)` there
is a circuit with `O(r(1 + log(1/ε))/√p₀)` queries that, with probability at least `1 − ε`, outputs
`ΠV|0⟩/√p`, and otherwise reports failure.

**Formalization Note** The algorithm is stated in unitary form: `U` has `N` output wires, a flag wire
and `t` work wires. The part of the final state with the flag `true` is `(ΠV|0⟩/√p) ⊗ g` with
`∥g∥² ≥ 1 − ε`, and flag `false` reports failure. The global sign of the source's proof is absorbed by
`g`. The constant in `O(·)` is absolute. `U` is fixed before the oracles, and `g` may depend on them. -/
theorem lemma_2_8 :
    ∃ C : ℝ, 0 < C ∧ ∀ {r : ℕ} (a : Fin r → ℕ) (N : ℕ) (V : OracleCircuit UnitaryGates a N)
      (P : Matrix (Qubits N) (Qubits N) ℂ), P.IsHermitian → P * P = P →
      ∀ p₀ : ℝ, 0 < p₀ → p₀ ≤ 1 → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (t : ℕ) (U : OracleCircuit UnitaryGates a (N + 1 + t)),
        (totalQueries U : ℝ) ≤
          C * totalQueries V * (1 + Real.log (1 / ε)) / Real.sqrt p₀ ∧
        ∀ orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ,
          (∀ k, orc k ∈ Matrix.unitaryGroup (Qubits (a k)) ℂ) →
          p₀ ≤ ‖act P (act (V.unitary orc) (zeroKet N))‖ ^ 2 →
          ∃ g : EuclideanSpace ℂ (Qubits t), 1 - ε ≤ ‖g‖ ^ 2 ∧
            ∀ (x : Qubits N) (y : Qubits t),
              act (U.unitary orc) (zeroKet (N + 1 + t))
                  (Fin.append (Fin.append x (fun _ : Fin 1 => true)) y) =
                act P (act (V.unitary orc) (zeroKet N)) x /
                    ‖act P (act (V.unitary orc) (zeroKet N))‖ * g y := by sorry

end QuarticGap
