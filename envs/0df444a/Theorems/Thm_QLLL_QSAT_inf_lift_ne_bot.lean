-- Prove2me | Theorems.Thm_QLLL_QSAT_inf_lift_ne_bot
-- name    : QLLL.QSAT.inf_lift_ne_bot
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:46:57.295983+00:00
-- url     : https://prove2.me/theorems/99f7af99-d3a8-49f5-bc95-2b87c1f960f2
-- title:
--   Quantum local lemma for $k$-QSAT with local satisfying spaces of dimension at least $2^k - r$
-- statement:
--   Model the state space of $n$ qubits as $\mathcal{H}_n = \mathbb{C}^{\{0,1\}^n}$, the functions from bit strings to $\mathbb{C}$, and for a subspace $X \subseteq \mathcal{H}_n$ write $\mathrm{R}(X) = \dim X / 2^n$ for its relative dimension. For a set $S$ of qubits and a subspace $Y$ of the local space $\mathbb{C}^{\{0,1\}^S}$, let $\mathrm{lift}_S(Y) \subseteq \mathcal{H}_n$ be the space of states all of whose $S$-slices (obtained by fixing the bits outside $S$) lie in $Y$; in tensor language this is $Y \otimes \mathbb{C}^{\{0,1\}^{S^c}}$.
--
--   Let $S_1, \dots, S_m$ be sets of qubits with $|S_i| = k$, and for each $i$ let $Y_i \subseteq \mathbb{C}^{\{0,1\}^{S_i}}$ be a local subspace with $\dim Y_i \ge 2^k - r$ (the satisfying space of a constraint of rank at most $r$ on the qubits $S_i$). Suppose every qubit belongs to at most $D' + 1$ of the sets $S_i$ and
--   $$\frac{r}{2^{k}} \cdot e \cdot (k D' + 1) \ \le\ 1.$$
--   Then
--   $$\bigcap_{i=1}^{m} \mathrm{lift}_{S_i}(Y_i) \ \neq\ \{0\}.$$
--
--   This is Corollary 16 of Ambainis, Kempe and Sattath phrased in terms of the local satisfying spaces: a $k$-QSAT instance whose constraints have rank at most $r$ and in which every qubit is acted on by at most $D' + 1$ constraints has a nonzero satisfying state.
--
--   **Formalization Note** $2^k - r$ is truncated subtraction of natural numbers. The paper's hypothesis "every qubit appears in at most $D = 2^k/(e r k)$ projectors" implies the condition above with $D' = D - 1$. Qubits are modelled as functions on bit strings, $(\{0,1\}^n \to \mathbb{C})$, rather than by Mathlib's `PiTensorProduct`. The identification of the two models is proved in the source project (`QuantumLocalLemma/Quantum/KQSAT/QubitTensor.lean`) and enters the platform inside the proof of `QLLL.PiQSAT.inf_extend_ne_bot`, the statement of the corollary on Mathlib's tensor product.
-- source:
--   A. Ambainis, J. Kempe, O. Sattath, A Quantum Lovász Local Lemma, J. ACM 59(5):24 (2012), arXiv:0911.1696 (numbering of the arXiv version), Corollary 16

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_Basic
import Mathlib

open QLLL
open QLLL.QSAT
open Finset Module
variable {n : ℕ}

theorem QLLL.QSAT.inf_lift_ne_bot {m : ℕ} {Sq : Fin m → Finset (Fin n)}
    {Y : (i : Fin m) → Submodule ℂ (HIn (Sq i))} {k r D' : ℕ}
    (hcard : ∀ i, (Sq i).card = k)
    (hrank : ∀ i, 2 ^ k - r ≤ Module.finrank ℂ (Y i))
    (hdeg : ∀ v : Fin n, (univ.filter fun i => v ∈ Sq i).card ≤ D' + 1)
    (hp : ((r : ℝ) / 2 ^ k) * Real.exp 1 * (((k * D' : ℕ) : ℝ) + 1) ≤ 1) :
    univ.inf (fun i => lift (Sq i) (Y i)) ≠ ⊥ := by sorry
