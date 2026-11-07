-- Prove2me | Theorems.Thm_SYKEdge_lemma_4_4
-- name    : SYKEdge.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:07:07.561286+00:00
-- url     : https://prove2.me/theorems/fc5b3c20-096c-42cc-b3e7-64ac5d406a69
-- title:
--   Lemma 4.4 — twisted bosons: $a_Sa_T=\varepsilon_{S,T}a_Ta_S$, $a_Sa_T^*-\varepsilon_{S,T}a_T^*a_S=1(S=T)\mathrm{Id}$, level shifts, $\sum_Sa_S^*a_S=N$
-- statement:
--   Let $\mathcal H=(S_1,\dots,S_m)$ be a $k$-uniform hypergraph and $a_i=K_ib_i$, $a_i^*=K_ib_i^*$ the twisted bosonic operators on $\mathcal F$. For all $S,T\in\mathcal H$:
--
--   1. $a_Sa_T=\varepsilon_{S,T}\,a_Ta_S$;
--   2. $a_Sa_T^*-\varepsilon_{S,T}\,a_T^*a_S=1(S=T)\cdot\mathrm{Id}$;
--   3. $a_S(\mathcal F_t)\subseteq\mathcal F_{t-1}$ for $t\ge1$, $a_S(\mathcal F_0)=0$, and $a_S^*(\mathcal F_t)\subseteq\mathcal F_{t+1}$ for $t\ge0$;
--   4. $a_S^*a_Sf_r=r_Sf_r$ for every occupation vector $r$, and consequently $\sum_{S\in\mathcal H}a_S^*a_S=N$.
--
--   The twisted bosons thus reproduce, as commutation phases, the signs $\varepsilon_{S,T}$ with which Majorana monomials commute.
--
--   **Formalization Note** Hyperedges are indexed by `Fin m`; $1(S=T)$ is equality of indices.
--
--   Differences from the source:
--   - encoding: the §3 standing assumptions (n ⩾ k ⩾ 2 even, ℋ a k-uniform hypergraph) → IsKUniform n k m S: the same, with ℋ = (S_1, …, S_m) an indexed list and m ⩾ 1; reason: repeated hyperedges are distinct elements (footnote 6); m ⩾ 1 is needed for |ℋ|^{−1/2} and only excludes the empty hypergraph
--   - encoding: 1(S = T) for S, T ∈ ℋ → if i = j (equality of indices); reason: ℋ is a list whose repeated hyperedges are distinct elements with independent disorder (footnote 6)
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Lemma 4.4, p.22

import Mathlib
import Definitions.Def_SYKEdge_Fock
import Definitions.Def_SYKEdge_Hamiltonian

namespace SYKEdge

/-- **Lemma 4.4**, A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.22.

The twisted bosonic operators `{a_S}_{S∈H}` on `F` satisfy, for all `S, T ∈ H`:
(1) `a_S a_T = ε_{S,T} a_T a_S`;
(2) `a_S a_T* − ε_{S,T} a_T* a_S = 1(S = T)·Id`;
(3) `a_S(F_t) ⊆ F_{t−1}` for all `t ⩾ 1`, `a_S(F₀) = 0`, and `a_S*(F_t) ⊆ F_{t+1}` for all `t ⩾ 0`;
(4) `a_S* a_S f_r = r_S f_r` for all `r ∈ ℤ^H_{⩾0}`, and consequently `Σ_{S∈H} a_S* a_S = N`.

**Formalization Note.** `H = (S₁, …, S_m)` is an indexed `k`-uniform hypergraph under the §3 standing
assumptions (`IsKUniform`); `1(S = T)` is equality of indices (footnote 6, p.3: repeated hyperedges are
distinct elements of `H`). -/
theorem lemma_4_4 {n k m : ℕ} (S : Fin m → Finset (Fin n)) (hS : IsKUniform n k m S) :
    (∀ i j : Fin m,
      aop S i ∘ₗ aop S j = ((eps (S i) (S j) : ℤ) : ℂ) • (aop S j ∘ₗ aop S i)) ∧
    (∀ i j : Fin m,
      aop S i ∘ₗ adag S j - ((eps (S i) (S j) : ℤ) : ℂ) • (adag S j ∘ₗ aop S i) =
        (if i = j then LinearMap.id else 0)) ∧
    (∀ i : Fin m,
      (∀ t : ℕ, 1 ≤ t → ∀ ψ ∈ fockLevel m t, aop S i ψ ∈ fockLevel m (t - 1)) ∧
      (∀ ψ ∈ fockLevel m 0, aop S i ψ = 0) ∧
      (∀ t : ℕ, ∀ ψ ∈ fockLevel m t, adag S i ψ ∈ fockLevel m (t + 1))) ∧
    (∀ i : Fin m, ∀ r : Fin m → ℕ,
      (adag S i ∘ₗ aop S i) (fbasis r) = ((r i : ℕ) : ℂ) • fbasis r) ∧
    ∑ i, adag S i ∘ₗ aop S i = numTot m := by sorry

end SYKEdge
