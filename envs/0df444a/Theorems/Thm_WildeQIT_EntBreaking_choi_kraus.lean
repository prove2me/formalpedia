-- Prove2me | Theorems.Thm_WildeQIT_EntBreaking_choi_kraus
-- name    : WildeQIT.EntBreaking.choi_kraus
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:03.748903+00:00
-- url     : https://prove2.me/theorems/28166618-2c5b-49d1-9a59-dafb1461eb8e
-- title:
--   Theorem 4.4.1 (Choi–Kraus) — channels are exactly the maps with a Kraus decomposition, and $d\le d_Ad_B$ operators suffice
-- statement:
--   Let $\mathcal H_A,\mathcal H_B$ be finite-dimensional Hilbert spaces with $d_A=\dim\mathcal H_A$, $d_B=\dim\mathcal H_B$, and let $\mathcal N:\mathcal L(\mathcal H_A)\to\mathcal L(\mathcal H_B)$ be a linear map.
--
--   1. $\mathcal N$ is completely positive and trace preserving if and only if there are a number $d$ and operators $V_0,\dots,V_{d-1}\in\mathcal L(\mathcal H_A,\mathcal H_B)$ with
--   $$
--   \mathcal N(X_A)=\sum_{l=0}^{d-1}V_lX_AV_l^\dagger\ \ \text{for all }X_A,\qquad \sum_{l=0}^{d-1}V_l^\dagger V_l=I_A .
--   $$
--   2. If $\mathcal N$ is completely positive and trace preserving, such a decomposition exists with $d\le d_Ad_B$.
--
--   This is the Choi–Kraus representation theorem: the axiomatic description of quantum evolutions (linearity, complete positivity, trace preservation) coincides with the Kraus form used throughout the book.
--
--   **Formalization Note** $\mathcal N$ is a $\mathbb C$-linear map between matrix spaces indexed by finite types; complete positivity quantifies over references $\mathbb C^r$ for every $r$.
--
--   Differences from the source:
--   - encoding: a map $\mathcal N$ for which linearity is one clause of the iff → $\mathcal N$ is a $\mathbb C$-linear map; reason: complete positivity (Definition 4.4.2) is defined only for linear maps, and a map with a Kraus decomposition is linear, so the only maps left out are non-linear ones, for which both sides of the book's iff are false.
--   - encoding: a reference system $R$ of arbitrary size → references $\mathbb C^r$ for every $r\in\mathbb N$; reason: every finite-dimensional reference is isomorphic to some $\mathbb C^r$.
--   - reading: "if and only if it has a Choi–Kraus decomposition …, and $d$ need not be any larger than $\dim(\mathcal H_A)\dim(\mathcal H_B)$" → the iff with any finite $d$, together with: every channel has a decomposition with $d\le d_Ad_B$; reason: the clause bounds how many Kraus operators are needed, not how many are allowed; this reading contains both the iff for every $d$ and the bound.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 4.4.1, p. 151

import Mathlib
import Definitions.Def_WildeQIT_EntBreaking_IsQuantumChannel
import Definitions.Def_WildeQIT_EntBreaking_IsChoiKrausDecomposition

namespace WildeQIT.EntBreaking

/-- **Theorem 4.4.1 (Choi–Kraus)**, Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, p. 151: "A map `N : L(ℋ_A) → L(ℋ_B)` is linear, completely positive, and
trace-preserving if and only if it has a Choi–Kraus decomposition `N(X_A) = ∑_{l=0}^{d−1} V_l X_A V_l†`
(4.188) … `∑_{l=0}^{d−1} V_l† V_l = I_A` (4.189), and `d` need not be any larger than
`dim(ℋ_A) dim(ℋ_B)`."

For a linear map `N`:
1. `N` is a quantum channel (completely positive and trace preserving) if and only if it has a
   Choi–Kraus decomposition with some finite number `d` of Kraus operators;
2. if `N` is a quantum channel, a decomposition exists with `d ≤ dim(ℋ_A) dim(ℋ_B)`.

**Formalization Note.** `N` is a `ℂ`-linear map, so the book's "linear" clause is carried by the
type; a map with a Choi–Kraus decomposition is linear, so the only maps not covered are non-linear
ones, for which both sides of the book's iff are false. The Kraus index set is `Fin d`, the book's
`{0, …, d−1}`; `dim(ℋ_A) = Fintype.card a`. -/
theorem choi_kraus {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    (N : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ) :
    (IsQuantumChannel N ↔ ∃ (d : ℕ) (V : Fin d → Matrix b a ℂ), IsChoiKrausDecomposition N V) ∧
    (IsQuantumChannel N → ∃ (d : ℕ) (V : Fin d → Matrix b a ℂ),
      IsChoiKrausDecomposition N V ∧ d ≤ Fintype.card a * Fintype.card b) := by sorry

end WildeQIT.EntBreaking
