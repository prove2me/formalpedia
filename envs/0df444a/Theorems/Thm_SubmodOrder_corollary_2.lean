-- Prove2me | Theorems.Thm_SubmodOrder_corollary_2
-- name    : SubmodOrder.corollary_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:37:32.388586+00:00
-- url     : https://prove2.me/theorems/e575503c-df62-4193-8299-4f3c5fb2da14
-- title:
--   Corollary 2 — $f(A)\le f(E(m))+\sum_\ell f(O_\ell\mid E(\ell-1))$ (corrected: interleaving)
-- statement:
--   Let $f$ be a set function with weak submodular order $\pi$ and let $A$ be a set with interleaved partition $\{O_\ell,E_\ell\}_{\ell=1}^m$. Then
--
--   $$
--   f(A)\ \le\ f(E(m))+\sum_{\ell\in[m]} f\bigl(O_\ell\ \big|\ E(\ell-1)\bigr),\qquad E(j)=\bigcup_{i\le j}E_i,\ E(0)=\emptyset .
--   $$
--
--   This is Lemma 1 for the identity permutation $\sigma(\ell)=\ell$. It is the bound used in the proof of Theorem 2, with $E_j$ the $j$-th element added by Threshold Add.
--
--   **Formalization Note** Blocks are 0-based in Lean; the identity permutation is substituted, so $L_\sigma(\ell)$ does not appear.
--
--   Differences from the source:
--   - correction: an interleaved partition {O₁, E₁, …, O_m, E_m} of A satisfies, for every ℓ ≥ 1, r_π(O_ℓ) < l_π(E_ℓ) ≤ r_π(E_ℓ) < r_π(O_{ℓ+1}) → the blocks cover A and, in the sequence O₁, E₁, O₂, …, O_m, E_m, every element of an earlier block has a smaller π-index than every element of a later block (the prose "alternate and never cross"); empty blocks are allowed; reason: the printed formula bounds only r_π(O_{ℓ+1}) and the statement is false under it: N = {x < a < b < c < d}, f(S) = ½[S ∩ {x,b,d} ≠ ∅] + ½[{x,d} ⊆ S] is monotone and subadditive with f(∅) = 0 and π a weak submodular order, O₁ = {a}, E₁ = {b}, O₂ = {x,c}, E₂ = {d} satisfies the formula, and the bound reads 1 = f(A) ≤ f({b,d}) + f({a} | ∅) + f({x,c} | {b}) = ½; empty blocks are used by the proof of Theorem 2 ("some sets may be empty")
--   - reading: l_π(S), r_π(S) (leftmost, rightmost element), undefined for S = ∅, in "π-nested" and "C to the right of A" → the comparisons π b < π a for all b, a in the two sets, which hold vacuously when a set is empty; reason: the paper applies the weak order with B = E(0) = ∅ (proof of Lemma 1, p.20)
--   - encoding: blocks indexed by ℓ ∈ [m], E(ℓ − 1) = ⋃_{i ≤ ℓ−1} E_i → blocks indexed by Fin m (0-based), E(ℓ − 1) = Eprefix E ℓ, E(m) = Eprefix E m; reason: index shift only
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, Corollary 2, p.20

import Mathlib
import Definitions.Def_SubmodOrder_marginal
import Definitions.Def_SubmodOrder_IsWeakSubmodularOrder
import Definitions.Def_SubmodOrder_IsInterleavedPartition

namespace SubmodOrder

/-- Corollary 2 (Udwani, arXiv:2107.02743v5, p.20): "Given a set function f with weak submodular
order π, set A with interleaved partition {Oℓ, Eℓ}_{ℓ=1}^m, and the permutation σ(ℓ) = ℓ for
every ℓ ∈ [m], we have f(A) ≤ f(E(m)) + ∑_{ℓ∈[m]} f(Oℓ | E(ℓ − 1))."

**Formalization Note.** Blocks are indexed by `Fin m` (0-based): the paper's `E(ℓ − 1)` for the
block `ℓ` is `Eprefix E ℓ`, and `E(m)` is `Eprefix E m`. The interleaved partition is the prose
reading "alternate and never cross" (`IsInterleavedPartition`; empty blocks allowed); under the
printed formula `rπ(Oℓ) < lπ(Eℓ) ≤ rπ(Eℓ) < rπ(Oℓ+1)` the corollary is false. -/
theorem corollary_2 {α : Type*} [DecidableEq α] {n m : ℕ} (f : Finset α → ℝ) (π : α ≃ Fin n)
    (hπ : IsWeakSubmodularOrder f π) (O E : Fin m → Finset α) (A : Finset α)
    (hA : IsInterleavedPartition π O E A) :
    f A ≤ f (Eprefix E m) + ∑ ℓ : Fin m, marginal f (O ℓ) (Eprefix E ℓ.val) := by sorry

end SubmodOrder
