-- Prove2me | Theorems.Thm_QLLL_QSAT_inf_ne_bot_of_degree_le
-- name    : QLLL.QSAT.inf_ne_bot_of_degree_le
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:46:14.497737+00:00
-- url     : https://prove2.me/theorems/bc945f6a-febb-419b-9f63-c2eb5b117fed
-- title:
--   Quantum local lemma for $k$-QSAT, function-model subspace form (Corollary 16)
-- statement:
--   Model the state space of $n$ qubits as $\mathcal{H}_n = \mathbb{C}^{\{0,1\}^n}$, the functions from bit strings to $\mathbb{C}$, and for a subspace $X \subseteq \mathcal{H}_n$ write $\mathrm{R}(X) = \dim X / 2^n$ for its relative dimension. For a set $S$ of qubits and a subspace $Y$ of the local space $\mathbb{C}^{\{0,1\}^S}$, let $\mathrm{lift}_S(Y) \subseteq \mathcal{H}_n$ be the space of states all of whose $S$-slices (obtained by fixing the bits outside $S$) lie in $Y$; in tensor language this is $Y \otimes \mathbb{C}^{\{0,1\}^{S^c}}$.
--
--   Let $X_1, \dots, X_m \subseteq \mathcal{H}_n$ be subspaces and $S_1, \dots, S_m$ sets of qubits such that:
--
--   1. each $X_i$ is cut out on $S_i$, that is, $X_i = \mathrm{lift}_{S_i}(Y_i)$ for some local subspace $Y_i$;
--   2. $|S_i| = k$ for every $i$;
--   3. $\mathrm{R}(X_i) \ge 1 - p$ for every $i$;
--   4. every qubit belongs to at most $D' + 1$ of the sets $S_i$;
--   5. $p \cdot e \cdot (k D' + 1) \le 1$.
--
--   Then
--   $$\bigcap_{i=1}^{m} X_i \ \neq\ \{0\}.$$
--
--   This is the function-model form of Corollary 16 of Ambainis, Kempe and Sattath, in which the corollary is proved; the forms on Mathlib's tensor product are derived from it. In the proof, each constraint shares qubits with at most $k D'$ others, Lemma 11 makes the others mutually R-independent, and Theorem 4 applies. With $p = r \cdot 2^{-k}$ and $D' + 1 = 2^k / (e r k)$ it recovers the corollary as stated.
--
--   The platform has four versions of Corollary 16: on Mathlib's tensor product, the operator form `QLLL.PiQSAT.inf_ker_extendOp_ne_bot` and the subspace form `QLLL.PiQSAT.inf_extend_ne_bot`; in the function model, the subspace form `QLLL.QSAT.inf_ne_bot_of_degree_le`, from which the others are derived, and the orthogonal-projector form `QLLL.QSAT.satisfiable_of_degree_le`.
--
--   **Formalization Note** Qubits are modelled as functions on bit strings, $(\{0,1\}^n \to \mathbb{C})$, rather than by Mathlib's `PiTensorProduct`. The identification of the two models is proved in the source project (`QuantumLocalLemma/Quantum/KQSAT/QubitTensor.lean`) and is used to derive `QLLL.PiQSAT.inf_extend_ne_bot`.
-- source:
--   A. Ambainis, J. Kempe, O. Sattath, A Quantum Lovász Local Lemma, J. ACM 59(5):24 (2012), arXiv:0911.1696 (numbering of the arXiv version), Corollary 16, subspace form used in its proof

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_Basic
import Mathlib

open QLLL
open QLLL.QSAT
open Finset Module
variable {n : ℕ}

theorem QLLL.QSAT.inf_ne_bot_of_degree_le {m : ℕ} {Sq : Fin m → Finset (Fin n)}
    {X : Fin m → Submodule ℂ (H n)} {k D' : ℕ} {p : ℝ}
    (hsupp : ∀ i, IsSupportedOn (Sq i) (X i))
    (hcard : ∀ i, (Sq i).card = k)
    (hX : ∀ i, 1 - p ≤ relDim (X i))
    (hdeg : ∀ v : Fin n, (univ.filter fun i => v ∈ Sq i).card ≤ D' + 1)
    (hp : p * Real.exp 1 * (((k * D' : ℕ) : ℝ) + 1) ≤ 1) :
    univ.inf X ≠ ⊥ := by sorry
