-- Prove2me | Theorems.Thm_QLLL_PiQSAT_inf_extend_ne_bot
-- name    : QLLL.PiQSAT.inf_extend_ne_bot
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:48:06.388355+00:00
-- url     : https://prove2.me/theorems/13175351-20f3-47c4-bf09-4a0c2de592eb
-- title:
--   Quantum local lemma for $k$-QSAT on $n$ qubits, subspace form (Corollary 16)
-- statement:
--   Let $\mathcal{Q} = \mathbb{C}^2$ be the single-qubit space and, for a finite set $T$ of qubits, let $\mathcal{Q}^{\otimes T} = \bigotimes_{j \in T} \mathcal{Q}$ be Mathlib's tensor power. For a set $S \subseteq \{1, \dots, n\}$ the $n$-qubit space splits as $\mathcal{Q}^{\otimes S} \otimes \mathcal{Q}^{\otimes S^c} \cong \mathcal{Q}^{\otimes n}$. Under this splitting a subspace $Y$ of the local space $\mathcal{Q}^{\otimes S}$ extends to $\mathrm{ext}_S(Y) = Y \otimes \mathcal{Q}^{\otimes S^c}$, and a local operator $P$ on $\mathcal{Q}^{\otimes S}$ extends to $P \otimes I$, where $I$ is the identity on the remaining qubits.
--
--   Let $S_1, \dots, S_m$ be sets of qubits and $Y_i \subseteq \mathcal{Q}^{\otimes S_i}$ local subspaces such that:
--
--   1. $|S_i| = k$ for every $i$;
--   2. $\dim Y_i / 2^k \ge 1 - p$ for every $i$;
--   3. every qubit belongs to at most $D' + 1$ of the sets $S_i$;
--   4. $p \cdot e \cdot (k D' + 1) \le 1$.
--
--   Then
--   $$\bigcap_{i=1}^{m} \mathrm{ext}_{S_i}(Y_i) \ \neq\ \{0\}.$$
--
--   This is Corollary 16 of Ambainis, Kempe and Sattath in its subspace form, stated with Mathlib's tensor product of qubits: local constraints that are large enough and do not overlap too much admit a common nonzero state. The platform has four versions of Corollary 16: on Mathlib's tensor product, the operator form `QLLL.PiQSAT.inf_ker_extendOp_ne_bot` and the subspace form `QLLL.PiQSAT.inf_extend_ne_bot`; in the function model, the subspace form `QLLL.QSAT.inf_ne_bot_of_degree_le`, from which the others are derived, and the orthogonal-projector form `QLLL.QSAT.satisfiable_of_degree_le`.
--
--   **Formalization Note** The qubit space is Mathlib's `PiTensorProduct` of `Fin 2 → ℂ`, and the extension to all qubits is built from Mathlib's `PiTensorProduct.tmulEquiv` and `PiTensorProduct.reindex`.
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

theorem QLLL.PiQSAT.inf_extend_ne_bot {m k D' : ℕ} {p : ℝ} (S : Fin m → Finset (Fin n))
    (Y : ∀ i, Submodule ℂ (Qubits {j // j ∈ S i}))
    (hcard : ∀ i, (S i).card = k)
    (hY : ∀ i, 1 - p ≤ (finrank ℂ (Y i) : ℝ) / 2 ^ k)
    (hdeg : ∀ v : Fin n, (Finset.univ.filter fun i => v ∈ S i).card ≤ D' + 1)
    (hp : p * Real.exp 1 * (((k * D' : ℕ) : ℝ) + 1) ≤ 1) :
    (⨅ i, extend (S i) (Y i)) ≠ ⊥ := by sorry
