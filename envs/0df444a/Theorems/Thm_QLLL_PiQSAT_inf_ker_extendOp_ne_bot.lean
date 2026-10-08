-- Prove2me | Theorems.Thm_QLLL_PiQSAT_inf_ker_extendOp_ne_bot
-- name    : QLLL.PiQSAT.inf_ker_extendOp_ne_bot
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:46:21.568974+00:00
-- url     : https://prove2.me/theorems/117ddb59-6e46-47f0-8d2a-801367e489f6
-- title:
--   Quantum local lemma for $k$-QSAT on $n$ qubits, operator form (Corollary 16)
-- statement:
--   Let $\mathcal{Q} = \mathbb{C}^2$ be the single-qubit space and, for a finite set $T$ of qubits, let $\mathcal{Q}^{\otimes T} = \bigotimes_{j \in T} \mathcal{Q}$ be Mathlib's tensor power. For a set $S \subseteq \{1, \dots, n\}$ the $n$-qubit space splits as $\mathcal{Q}^{\otimes S} \otimes \mathcal{Q}^{\otimes S^c} \cong \mathcal{Q}^{\otimes n}$. Under this splitting a subspace $Y$ of the local space $\mathcal{Q}^{\otimes S}$ extends to $\mathrm{ext}_S(Y) = Y \otimes \mathcal{Q}^{\otimes S^c}$, and a local operator $P$ on $\mathcal{Q}^{\otimes S}$ extends to $P \otimes I$, where $I$ is the identity on the remaining qubits.
--
--   Let $S_1, \dots, S_m$ be sets of qubits and $P_i$ linear operators on $\mathcal{Q}^{\otimes S_i}$ such that:
--
--   1. $|S_i| = k$ for every $i$;
--   2. $\operatorname{rank} P_i \le r$ for every $i$;
--   3. every qubit belongs to at most $D' + 1$ of the sets $S_i$;
--   4. $\dfrac{r}{2^{k}} \cdot e \cdot (k D' + 1) \le 1$.
--
--   Then there is a nonzero state annihilated by every extended constraint:
--   $$\bigcap_{i=1}^{m} \ker\,(P_i \otimes I) \ \neq\ \{0\}.$$
--
--   This is Corollary 16 of Ambainis, Kempe and Sattath, the quantum analogue of the Lovász local lemma for $k$-SAT: an instance of $k$-local constraints of rank at most $r$ in which every qubit takes part in few constraints is satisfiable. The usual case is that each $P_i$ is an orthogonal projector, but the statement holds for arbitrary local operators of rank at most $r$, since only the dimension of their kernels matters. The platform has four versions of Corollary 16: on Mathlib's tensor product, the operator form `QLLL.PiQSAT.inf_ker_extendOp_ne_bot` and the subspace form `QLLL.PiQSAT.inf_extend_ne_bot`; in the function model, the subspace form `QLLL.QSAT.inf_ne_bot_of_degree_le`, from which the others are derived, and the orthogonal-projector form `QLLL.QSAT.satisfiable_of_degree_le`.
--
--   **Formalization Note** Self-adjointness of the $P_i$ is not stated because the pinned Mathlib has no inner product on `PiTensorProduct`; it is not needed for the conclusion. The orthogonal-projector form, with the paper's exact hypotheses, is `QLLL.QSAT.satisfiable_of_degree_le`.
-- source:
--   Not in the paper; Mathlib PiTensorProduct formulation of Corollary 16 of Ambainis–Kempe–Sattath (arXiv:0911.1696), companion formalization, see blueprint https://sattath.github.io/Quantum-Lovasz-Local-Lemma/blueprint/

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_QubitTensor
import Definitions.Def_QLLL_Quantum_KQSAT_PiTensor
import Mathlib

open TensorProduct Module
open QLLL QLLL.QSAT QLLL.QubitTensor
open QLLL
open QLLL.PiQSAT
variable {n : ℕ}

theorem QLLL.PiQSAT.inf_ker_extendOp_ne_bot {m k r D' : ℕ} (S : Fin m → Finset (Fin n))
    (P : ∀ i, Module.End ℂ (Qubits {j // j ∈ S i}))
    (hcard : ∀ i, (S i).card = k)
    (hrank : ∀ i, finrank ℂ (LinearMap.range (P i)) ≤ r)
    (hdeg : ∀ v : Fin n, (Finset.univ.filter fun i => v ∈ S i).card ≤ D' + 1)
    (hp : ((r : ℝ) / 2 ^ k) * Real.exp 1 * (((k * D' : ℕ) : ℝ) + 1) ≤ 1) :
    (⨅ i, LinearMap.ker (extendOp (S i) (P i))) ≠ ⊥ := by sorry
