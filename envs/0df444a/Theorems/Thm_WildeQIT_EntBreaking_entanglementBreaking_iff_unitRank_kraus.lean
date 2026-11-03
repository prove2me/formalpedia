-- Prove2me | Theorems.Thm_WildeQIT_EntBreaking_entanglementBreaking_iff_unitRank_kraus
-- name    : WildeQIT.EntBreaking.entanglementBreaking_iff_unitRank_kraus
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:26.068617+00:00
-- url     : https://prove2.me/theorems/cc03bcd4-d182-42a2-86cd-cc713234e44a
-- title:
--   Theorem 4.6.1 — a channel is entanglement-breaking if and only if it has unit-rank Kraus operators
-- statement:
--   Let $\mathcal N:\mathcal L(\mathcal H_A)\to\mathcal L(\mathcal H_B)$ be a quantum channel between finite-dimensional Hilbert spaces. The following are equivalent:
--
--   1. $\mathcal N$ is entanglement breaking: for a reference system $R$ of every finite size and every state $\rho_{RA}$, the state $(\mathrm{id}_R\otimes\mathcal N)(\rho_{RA})$ is separable;
--   2. $\mathcal N$ has a Kraus representation with unit-rank Kraus operators: there are operators $V_0,\dots,V_{d-1}\in\mathcal L(\mathcal H_A,\mathcal H_B)$ with
--   $$
--   \mathcal N(X)=\sum_{l=0}^{d-1}V_lXV_l^\dagger,\qquad \sum_{l=0}^{d-1}V_l^\dagger V_l=I_A,\qquad \operatorname{rank}V_l=1\ \text{for every }l .
--   $$
--
--   Equivalently, each Kraus operator has the form $|\xi_l\rangle_B\langle\varphi_l|_A$ with nonzero vectors. The theorem turns the operational definition of entanglement breaking, a condition on all reference systems and all input states, into a condition on a single Kraus representation; Corollary 4.6.1 reads off the measure-and-prepare form from it.
--
--   **Formalization Note** "Unit rank" is rank exactly one, so a zero operator is not unit rank.
--
--   Differences from the source:
--   - encoding: a reference system $R$ of arbitrary size (Definition 4.6.8) → references $\mathbb C^r$ for every $r\in\mathbb N$; reason: every finite-dimensional reference is isomorphic to some $\mathbb C^r$.
--   - encoding: "a Kraus representation" → a Choi–Kraus decomposition (4.188)–(4.189) indexed by $\{0,\dots,d-1\}$ for some $d$; reason: the book's Kraus representations are the finite families of Theorem 4.4.1.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 4.6.1, p. 167; Definition 4.6.8, p. 166

import Mathlib
import Definitions.Def_WildeQIT_EntBreaking_IsQuantumChannel
import Definitions.Def_WildeQIT_EntBreaking_IsChoiKrausDecomposition
import Definitions.Def_WildeQIT_EntBreaking_IsEntanglementBreaking

namespace WildeQIT.EntBreaking

/-- **Theorem 4.6.1**, Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
p. 167: "A channel is entanglement-breaking if and only if it has a Kraus representation with
Kraus operators that are unit rank."

Let `N : L(ℋ_A) → L(ℋ_B)` be a quantum channel. Then `id_R ⊗ N` sends every state of `RA` to a
separable state of `RB`, for references `R` of every finite size (Definition 4.6.8), if and only if
`N` has a Choi–Kraus decomposition `N(X) = ∑_l V_l X V_l†`, `∑_l V_l† V_l = I_A`, in which every
Kraus operator `V_l` has rank exactly one.

**Formalization Note.** "Unit rank" is `Matrix.rank (V l) = 1`, so a zero operator does not
count as unit rank. The Kraus index set is `Fin d` for some `d`. -/
theorem entanglementBreaking_iff_unitRank_kraus {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] (N : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ) (hN : IsQuantumChannel N) :
    IsEntanglementBreaking N ↔
      ∃ (d : ℕ) (V : Fin d → Matrix b a ℂ),
        IsChoiKrausDecomposition N V ∧ ∀ l, (V l).rank = 1 := by sorry

end WildeQIT.EntBreaking
