-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_Supplement_theorem_A_1
-- name    : QAdvFew.PoQOracle.Supplement.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:25:53.161508+00:00
-- url     : https://prove2.me/theorems/ab5bf1c9-1cbe-46f6-9fb2-0c0be2a40438
-- title:
--   Theorem A.1 — $\mathsf{QCMA}^S\subseteq\mathsf{BQP}^{S,\mathsf{QCMA}^{\vec\sigma}}$ with probability $1$
-- statement:
--   Let $\vec\sigma=\{\sigma_t\}_{t\in\mathbb N}$ be any family of states, $\sigma_t$ on $t$ qubits, with a fixed purification of each $\sigma_t$ on $2t$ qubits, let $U_t\leftarrow\mathrm{Haar}(\{0,1\}^t)$ be independent, and let $S=\{S^{U_t}_{\sigma_t}\}_{t\in\mathbb N}$. Then with probability $1$ over $\{U_t\}_{t\in\mathbb N}$,
--
--   $$
--   \mathsf{QCMA}^S\subseteq\mathsf{BQP}^{S,\mathsf{QCMA}^{\vec\sigma}},
--   $$
--
--   as classes of promise problems: each promise problem in $\mathsf{QCMA}^S$ is decided by one QPT algorithm with access to $S$ and to an arbitrary oracle for the complete verification problem of $\mathsf{QCMA}^{\vec\sigma}$.
--
--   Consequently, if $\mathsf{BQP}^{\vec\sigma}=\mathsf{QCMA}^{\vec\sigma}$ then $\mathsf{BQP}^S=\mathsf{QCMA}^S$ almost surely (Corollary A.2): a collapse relative to a state-preparation channel lifts to the random unitary oracle $S$.
--
--   Differences from the source:
--   - encoding: any family σ⃗ of t-qubit states with fixed purifications on 2t qubits → every family of unit vectors φ t on t + t qubits (σ_t = the reduced state on the first t); reason: every t-qubit state has a purification on 2t qubits, so this ranges over every σ⃗ and every choice of purifications
--   - encoding: access to σ⃗: a channel returning a fresh copy of σ_t → a gate writing |φ_t⟩ onto fresh wires whose purifying half is never touched again (well-formedness), costing t; reason: a copy of σ_t is the first half of its purification
--   - encoding: an oracle for QCMA^{σ⃗}: given a verifier and a runtime bound in unary, decide the promise; arbitrary outside it → any classical oracle answering 1 / 0 on the codes of yes / no instances (m, k, out, circuit, 1^T) and anything elsewhere; reason: Lean representation of the complete verification promise problem
--   - reading: the class BQP^{S, QCMA^{σ⃗}} for an oracle whose behavior outside the promise is arbitrary → one uniform QPT algorithm that is correct for every such oracle (∃ algorithm ∀ oracle); reason: the paper's algorithm is fixed and correct whatever the oracle answers outside the promise; this is the stronger reading
--   - encoding: U_t ← Haar({0,1}^t) independently; with probability 1 → ∀ᵐ U ∂haarFamily, the infinite product of the normalized Haar measures; reason: Lean representation
--   - encoding: QPT/nonuniform QPT algorithms and parties with oracle access, as in §3.2.1–§3.2.2 → uniform (resp. arbitrary) polynomially bounded families of Clifford+T circuits with classical-oracle gates and controlled/inverse unitary-oracle gates; size = binary description length plus t per level-t query; component/level superposition via controlled queries; reason: Lean representation of the paper's conventions; polynomially equivalent
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Theorem A.1, p. 51 (PDF p. 53)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Supplement_AppA
import Definitions.Def_QAdvFew_PoQOracle_Supplement_QCMAU

open QAlgorithms.Complexity MeasureTheory

namespace QAdvFew.PoQOracle.Supplement

/-- **Theorem A.1** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Theorem A.1, p. 51 (PDF p. 53)): "With probability 1 over `{U_t}_{t∈ℕ}`,
`QCMA^S ⊆ BQP^{S,QCMA^{σ⃗}}`."

For every family of `2t`-qubit unit vectors `φ t` (the fixed purifications of the `t`-qubit states
`σ_t`), for almost every family `U` of independent Haar unitaries `U_t` on `t` qubits, every promise
problem in `QCMA^S` (`S = {S^{U_t}_{σ_t}}_t`, `oracleS φ U`) is decided by one uniform QPT algorithm
with access to `S` and to **any** oracle for the complete verification problem of `QCMA^{σ⃗}`.

**Formalization Note** Promise classes (p. 51: "Throughout this section, complexity classes refer to
promise problems"). Every state `σ_t` on `t` qubits has a purification on `2t` qubits, so ranging
over unit vectors `φ t` ranges over every `σ⃗` with every choice of purifications. Level-`t`
queries and copies of `σ_t` are charged `t`; controlled queries to `S` are allowed. -/
theorem theorem_A_1 (φ : (t : ℕ) → QState (t + t)) (hφ : ∀ t, Normalized (φ t)) :
    ∀ᵐ U ∂haarFamily,
      PromiseQCMAU (oracleS φ U) (fun _ => false) ⊆
        PromiseBQPUForAll (oracleS φ U) (IsQCMASigmaOracle φ) := by sorry

end QAdvFew.PoQOracle.Supplement
