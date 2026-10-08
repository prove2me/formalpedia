-- Prove2me | Theorems.Thm_QLLL_QSAT_satisfiable_of_degree_le
-- name    : QLLL.QSAT.satisfiable_of_degree_le
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:46:07.956064+00:00
-- url     : https://prove2.me/theorems/61b794bd-d971-4415-ba1c-44596db9c6f8
-- title:
--   $k$-QSAT with orthogonal projectors of rank at most $r$ and bounded qubit degree is satisfiable (Corollary 16, the paper's setting)
-- statement:
--   Model the state space of $n$ qubits as $\mathcal{H}_n = \mathbb{C}^{\{0,1\}^n}$. A $k$-QSAT instance on $n$ qubits consists of constraints $i = 1, \dots, m$, each given by a set $q_i$ of exactly $k$ qubits and a matrix $\Pi_i$ on $\mathbb{C}^{\{0,1\}^{q_i}}$ that is an orthogonal projector: idempotent ($\Pi_i^2 = \Pi_i$) and self-adjoint ($\Pi_i^\dagger = \Pi_i$). The instance is *satisfiable* if there is a nonzero state $\psi \in \mathcal{H}_n$ with $(\Pi_i \otimes I)\psi = 0$ for every $i$, where $I$ is the identity on the remaining qubits.
--
--   Suppose every $\Pi_i$ has rank at most $r$, every qubit belongs to at most $D' + 1$ of the sets $q_i$, and
--   $$\frac{r}{2^{k}} \cdot e \cdot (k D' + 1) \ \le\ 1.$$
--   Then the instance is satisfiable.
--
--   This is Corollary 16 of Ambainis, Kempe and Sattath for $k$-QSAT instances given by projectors, the quantum analogue of Corollary 2 for $k$-SAT with the same parameters. For rank-one projectors it gives Corollary 5. It is the form in the paper's exact physical setting and the only form on the platform that states self-adjointness of the constraints. The platform has four versions of Corollary 16: on Mathlib's tensor product, the operator form `QLLL.PiQSAT.inf_ker_extendOp_ne_bot` and the subspace form `QLLL.PiQSAT.inf_extend_ne_bot`; in the function model, the subspace form `QLLL.QSAT.inf_ne_bot_of_degree_le`, from which the others are derived, and the orthogonal-projector form `QLLL.QSAT.satisfiable_of_degree_le`.
--
--   **Formalization Note** The paper's hypothesis "every qubit appears in at most $D = 2^k/(e r k)$ projectors" implies the condition above with $D' = D - 1$. Qubits are modelled as functions on bit strings, $(\{0,1\}^n \to \mathbb{C})$, rather than by Mathlib's `PiTensorProduct`. The identification of the two models is proved in the source project (`QuantumLocalLemma/Quantum/KQSAT/QubitTensor.lean`) and is used for the forms on Mathlib's tensor product. The projector condition is Mathlib's `IsStarProjection`. Self-adjointness cannot yet be stated for the tensor-product forms because the pinned Mathlib has no inner product on `PiTensorProduct`.
-- source:
--   A. Ambainis, J. Kempe, O. Sattath, A Quantum Lovász Local Lemma, J. ACM 59(5):24 (2012), arXiv:0911.1696 (numbering of the arXiv version), Corollary 16 (and Corollary 5 for rank one)

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_Projector
import Mathlib

open QLLL
open QLLL.QSAT
open scoped Matrix Kronecker
open WithLp (toLp ofLp)
variable {n : ℕ}

theorem QLLL.QSAT.satisfiable_of_degree_le {k r D' : ℕ} (I : QSATInstance n k)
    (hrank : ∀ i, (I.proj i).rank ≤ r)
    (hdeg : ∀ v : Fin n,
      (Finset.univ.filter fun i => v ∈ I.qubits i).card ≤ D' + 1)
    (hp : ((r : ℝ) / 2 ^ k) * Real.exp 1 * (((k * D' : ℕ) : ℝ) + 1) ≤ 1) :
    I.Satisfiable := by sorry
