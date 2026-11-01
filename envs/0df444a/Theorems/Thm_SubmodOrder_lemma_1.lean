-- Prove2me | Theorems.Thm_SubmodOrder_lemma_1
-- name    : SubmodOrder.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:37:37.5011+00:00
-- url     : https://prove2.me/theorems/2ff248db-5b72-4068-ab64-0ec864952349
-- title:
--   Lemma 1 — the interleaved-partition bound $f(A)\le f(E(m))+\sum_\ell f(O_\ell\mid L_\sigma(\ell)\cup E(\ell-1))$ (corrected: interleaving)
-- statement:
--   Let $f$ be a set function with weak submodular order $\pi$, let $A$ be a set with interleaved partition $\{O_\ell,E_\ell\}_{\ell=1}^m$, and let $\sigma:[m]\to[m]$ be a permutation. Then
--
--   $$
--   f(A)\ \le\ f(E(m))+\sum_{\ell\in[m]} f\bigl(O_\ell\ \big|\ L_\sigma(\ell)\cup E(\ell-1)\bigr),
--   $$
--
--   where $E(j)=\bigcup_{i\le j}E_i$ and $L_\sigma(\ell)$ is the union of the blocks $O_i$ with $i<\ell$ and $O_i\subseteq O_\sigma(\ell)=\bigcup_{\sigma(i')\ge\sigma(\ell)}O_{i'}$.
--
--   For a submodular function the bound $f(A)\le f(E(m))+f(O(1)\mid E(m))$ holds, but for submodular order functions it can fail; Lemma 1 replaces it by a family of incomparable bounds, one for each $\sigma$. Its specializations (Corollaries 2 and 3) drive the analysis of all the algorithms of the paper.
--
--   **Formalization Note** No monotonicity, subadditivity or normalization is assumed, as in the paper. Blocks are 0-based in Lean.
--
--   Differences from the source:
--   - correction: an interleaved partition {O₁, E₁, …, O_m, E_m} of A satisfies, for every ℓ ≥ 1, r_π(O_ℓ) < l_π(E_ℓ) ≤ r_π(E_ℓ) < r_π(O_{ℓ+1}) → the blocks cover A and, in the sequence O₁, E₁, O₂, …, O_m, E_m, every element of an earlier block has a smaller π-index than every element of a later block (the prose "alternate and never cross"); empty blocks are allowed; reason: the printed formula bounds only r_π(O_{ℓ+1}) and the statement is false under it: N = {x < a < b < c < d}, f(S) = ½[S ∩ {x,b,d} ≠ ∅] + ½[{x,d} ⊆ S] is monotone and subadditive with f(∅) = 0 and π a weak submodular order, O₁ = {a}, E₁ = {b}, O₂ = {x,c}, E₂ = {d} satisfies the formula, and the bound reads 1 = f(A) ≤ f({b,d}) + f({a} | ∅) + f({x,c} | {b}) = ½; empty blocks are used by the proof of Theorem 2 ("some sets may be empty")
--   - reading: l_π(S), r_π(S) (leftmost, rightmost element), undefined for S = ∅, in "π-nested" and "C to the right of A" → the comparisons π b < π a for all b, a in the two sets, which hold vacuously when a set is empty; reason: the paper applies the weak order with B = E(0) = ∅ (proof of Lemma 1, p.20)
--   - encoding: blocks indexed by ℓ ∈ [m], E(ℓ − 1) = ⋃_{i ≤ ℓ−1} E_i, σ : [m] → [m] a permutation → blocks indexed by Fin m (0-based), E(ℓ − 1) = Eprefix E ℓ, E(m) = Eprefix E m, σ : Equiv.Perm (Fin m); reason: index shift only
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, Lemma 1, p.19 (proof pp.19–20)

import Mathlib
import Definitions.Def_SubmodOrder_marginal
import Definitions.Def_SubmodOrder_IsWeakSubmodularOrder
import Definitions.Def_SubmodOrder_IsInterleavedPartition
import Definitions.Def_SubmodOrder_Lsigma

namespace SubmodOrder

/-- Lemma 1 (Udwani, *Submodular Order Functions and Assortment Optimization*,
arXiv:2107.02743v5, p.19; proof pp.19–20): "Given a set function f with weak submodular order π,
set A with interleaved partition {Oℓ, Eℓ}_{ℓ=1}^m, and a permutation σ : [m] → [m], we have
f(A) ≤ f(E(m)) + ∑_{ℓ∈[m]} f(Oℓ | Lσ(ℓ) ∪ E(ℓ − 1))."

**Formalization Note.** Blocks are indexed by `Fin m` (0-based), so the paper's `E(ℓ − 1)` for
the block `ℓ` is `Eprefix E ℓ` and `E(m)` is `Eprefix E m`. The interleaved partition is the
prose reading "alternate and never cross" (`IsInterleavedPartition`; empty blocks allowed): the
printed formula `rπ(Oℓ) < lπ(Eℓ) ≤ rπ(Eℓ) < rπ(Oℓ+1)` admits partitions for which the lemma is
false. No monotonicity, subadditivity or `f ∅ = 0` is assumed, as in the paper. -/
theorem lemma_1 {α : Type*} [DecidableEq α] {n m : ℕ} (f : Finset α → ℝ) (π : α ≃ Fin n)
    (hπ : IsWeakSubmodularOrder f π) (O E : Fin m → Finset α) (A : Finset α)
    (hA : IsInterleavedPartition π O E A) (σ : Equiv.Perm (Fin m)) :
    f A ≤ f (Eprefix E m) + ∑ ℓ : Fin m, marginal f (O ℓ) (Lsigma O σ ℓ ∪ Eprefix E ℓ.val) := by sorry

end SubmodOrder
