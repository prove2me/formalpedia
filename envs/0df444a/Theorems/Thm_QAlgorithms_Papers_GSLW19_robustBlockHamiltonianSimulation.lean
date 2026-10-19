-- Prove2me | Theorems.Thm_QAlgorithms_Papers_GSLW19_robustBlockHamiltonianSimulation
-- name    : QAlgorithms.Papers.GSLW19.robustBlockHamiltonianSimulation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T18:49:03.382984+00:00
-- url     : https://prove2.me/theorems/a45c43aa-b280-43a7-870f-187844176447
-- title:
--   GSLW Corollary 62: robust block-Hamiltonian simulation
-- statement:
--   This is the robust block-Hamiltonian simulation result of Gilyén, Su, Low and Wiebe (Corollary 62 of arXiv:1806.01838v1, Corollary 63 in the published version).
--
--   Block-encodings are as in Definition 43: an $(a+s)$-qubit unitary $U$ is an $(\alpha,a,\eta)$-block-encoding of an $s$-qubit operator $H$ if $\|H-\alpha(\langle0|^{\otimes a}\otimes I)U(|0\rangle^{\otimes a}\otimes I)\|\le\eta$ in operator norm.
--
--   There is an absolute constant $C>0$ such that the following holds. Let $s,a\in\mathbb N$, $t\in\mathbb R$, $\varepsilon\in(0,1)$ and $\alpha>0$. Then there exist $w\le C$ and a circuit on $(a+2)+s+w$ qubits, made of two-qubit gates and calls to a black box $U$ on $a+s$ qubits, using
--
--   1. at most $6\alpha|t|+9\ln(12/\varepsilon)$ uncontrolled applications of $U$ or $U^\dagger$,
--   2. at most $3$ applications of controlled-$U$ or its inverse,
--   3. at most $C(a+1)\big(\alpha|t|+\ln(2/\varepsilon)\big)$ two-qubit gates,
--
--   such that for every Hermitian $s$-qubit matrix $H$ and every $(\alpha,a,\varepsilon/|2t|)$-block-encoding $U$ of $H$, the circuit (with its last $w$ qubits as clean ancillas) implements a unitary $V$ that is a
--
--   $$
--   (1,\;a+2,\;\varepsilon)\text{-block-encoding of } e^{itH}.
--   $$
--
--   This gives Hamiltonian simulation with additive query complexity in $\alpha|t|$ and $\log(1/\varepsilon)$, robust to an imprecise block-encoding of the Hamiltonian.
--
--   **Formalization Note** The circuit may depend on $s,a,t,\varepsilon,\alpha$ but not on $H$ or $U$. The source's gate bound $O(a(\cdots))$ is encoded as $O((a+1)(\cdots))$, since the two new ancillas need gates even when $a=0$. At $t=0$ the source's $\varepsilon/|2t|$ is undefined; in Lean $\varepsilon/0=0$, so there the hypothesis is an exact block-encoding.
-- source:
--   Quantum singular value transformation and beyond: exponential improvements for quantum matrix arithmetics (Gilyén, Su, Low, Wiebe), arXiv:1806.01838v1, Corollary 62, PDF p. 53. https://arxiv.org/abs/1806.01838v1 . PDF SHA-256: 0326a3de56b10c9805074031a827b1ac4c5ee526c5ad362096adfbacc261c60d.

import Definitions.Def_QAlgorithms_Defs_CircuitResources
set_option autoImplicit false

namespace QAlgorithms.Papers.GSLW19

open QAlgorithms


/-- **GSLW Corollary 62** (PDF p.53; Corollary 63 in the published version), robust
block-Hamiltonian simulation.

Let `t ∈ ℝ`, `ε ∈ (0, 1)` and let `U` be an `(α, a, ε/|2t|)`-block-encoding of the Hamiltonian
`H`. Then one can implement a unitary `V` which is a `(1, a + 2, ε)`-block-encoding of `e^{itH}`,
with `6α|t| + 9 log(12/ε)` uses of `U` or its inverse, `3` uses of controlled-`U` or its inverse,
`O(a(α|t| + log(2/ε)))` two-qubit gates and `O(1)` ancilla qubits.

Encoding choices: `log` is the natural logarithm (the proof's `ln(12/ε)`); the circuit depends
on `s, a, t, ε, α` only (not on `H` or `U`); "`O(1)` ancilla qubits" is `w ≤ C` clean ancillas
beyond the `a + 2` encoding ancillas, with an absolute `C`; the gate bound
`O(a(α|t| + log(2/ε)))` is encoded as `C · (a + 1) · (α|t| + log(2/ε))` (at `a = 0` the literal
bound `0` is impossible, the proof via Theorem 56 gives `O((a + 1)d)`); "Hamiltonian" means
Hermitian. At `t = 0` the source's `ε/|2t|` is undefined; Lean's `ε/0 = 0` makes the hypothesis an
exact encoding there. -/
theorem robustBlockHamiltonianSimulation :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s a : ℕ) (t ε α : ℝ), 0 < ε → ε < 1 → 0 < α →
        ∃ (w : ℕ) (c : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => a + s) (a + 2 + s + w)),
          (w : ℝ) ≤ C ∧
          (c.plainQueryCount 0 : ℝ) ≤ 6 * α * |t| + 9 * Real.log (12 / ε) ∧
          c.controlledQueryCount 0 ≤ 3 ∧
          (c.gateCount : ℝ) ≤ C * ((a : ℝ) + 1) * (α * |t| + Real.log (2 / ε)) ∧
          ∀ (H : Matrix (Qubits s) (Qubits s) ℂ) (U : Matrix (Qubits (a + s)) (Qubits (a + s)) ℂ),
            H.IsHermitian → IsQubitBlockEncoding a s U α (ε / |2 * t|) H →
            ∃ V : Matrix (Qubits (a + 2 + s)) (Qubits (a + 2 + s)) ℂ,
              ImplementsWithCleanAncillas (c.unitary fun _ => U) V ∧
              IsQubitBlockEncoding (a + 2) s V 1 ε
                (NormedSpace.exp ((Complex.I * (t : ℂ)) • H)) := by
  sorry

end QAlgorithms.Papers.GSLW19
