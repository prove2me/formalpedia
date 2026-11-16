-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_Supplement_lemma_5_4
-- name    : SubadditiveMMS580.Amplification.Supplement.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:00:16.244206+00:00
-- url     : https://prove2.me/theorems/cd96746f-3506-4fc4-a20d-06829f827b8a
-- title:
--   Lemma 5.4 — cap and restore: $\|\tilde v\|_\infty+\max_{w(B)<\beta}\tilde v(B)\le A/(2A-\beta)$
-- statement:
--   Let $P$ be a nonempty finite set of goods, $w$ nonnegative additive coefficients on $P$, and
--   $$A=w(P)-\max_{g\in P}w(g).$$
--   If $0<\beta<A$, there are nonnegative coefficients $\tilde v$ on $P$ with $\tilde v(P)=1$ such that
--   $$\|\tilde v\|_\infty+\max_{B\subseteq P:\ w(B)<\beta}\tilde v(B)\le\frac{A}{2A-\beta}.\tag{23}$$
--   In particular, for every valuation $v$ with $w\le v$ ($w$ extended by zero outside $P$, i.e. $w(S\cap P)\le v(S)$ for all $S$), the choice $(\emptyset,\tilde v,A/(2A-\beta))$, with no reserved goods, satisfies condition (16) for $v$ and $\beta$.
--
--   It supplies the non-reserving choices of §5.4 in the proof of Theorem 1.3.
--
--   Differences from the source:
--   - generalization: v a valuation (normalized, monotone, ℝ≥0-valued) → v an arbitrary real set function; reason: Lemma 5.4 uses only w ≤ v and additivity of w; every source valuation is such a set function
--   - encoding: the maximum of ṽ(B) over B ⊆ P with w(B) < β → the bound for every B ⊆ P with w(B) < β; reason: the family is finite and contains ∅ (β > 0), so the maximum exists and the two forms are equivalent
--   - encoding: ṽ on P and ‖ṽ‖∞ = max over P → ṽ : Fin m → ℝ, zero outside P, and supNorm over all goods; reason: ṽ is nonnegative and P is nonempty, so the maximum over all goods equals the maximum over P
--   - reading: 'In particular, if w ≤ v, the choice … satisfies (16)' → the same ṽ works for every v with w ≤ v; reason: the source's ṽ is built from w and β alone, before any v is considered
-- source:
--   Bo Li, Ankang Sun, Toward Constant-Factor Maximin Share Guarantees for Subadditive Valuations, STOC 2027 submission #580 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/580.pdf, sha256 7de124b5706e9e49301a281a1eb418a8ae32d04bf4cf0941b969cc3cde85e485, Lemma 5.4, p. 33 (PDF p. 33)

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Supplement_Reservation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation

open MultiAllocToAlloc.Subadditive MeasureTheory

namespace SubadditiveMMS580.Amplification.Supplement

/-- Lemma 5.4 (Cap and restore; Li–Sun, STOC 2027 submission #580, p. 33): let `w` be nonnegative
additive coefficients on a nonempty finite set `P`, and `A = w(P) − max_{g ∈ P} w(g)`. If
`0 < β < A`, there are nonnegative coefficients `ṽ` on `P` (zero outside `P`) with `ṽ(P) = 1`
and `‖ṽ‖∞ + max_{B ⊆ P, w(B) < β} ṽ(B) ≤ A/(2A − β)` (23); in particular, for every `v` with
`w ≤ v` (`w` extended by zero outside `P`), the choice `(∅, ṽ, A/(2A − β))` satisfies (16). -/
theorem lemma_5_4 {m : ℕ} (P : Finset (Fin m)) (hP : P.Nonempty) (w : Fin m → ℝ)
    (hw : ∀ g ∈ P, 0 ≤ w g) (A : ℝ) (hA : A = ∑ g ∈ P, w g - P.sup' hP w)
    (β : ℝ) (hβ : 0 < β) (hβA : β < A) :
    ∃ vt : Fin m → ℝ, (∀ g, 0 ≤ vt g) ∧ (∀ g, g ∉ P → vt g = 0) ∧ ∑ g ∈ P, vt g = 1 ∧
      (∀ B : Finset (Fin m), B ⊆ P → ∑ g ∈ B, w g < β →
        supNorm vt + ∑ g ∈ B, vt g ≤ A / (2 * A - β)) ∧
      ∀ v : Finset (Fin m) → ℝ, (∀ S : Finset (Fin m), ∑ g ∈ S ∩ P, w g ≤ v S) →
        SatisfiesReservation v β ⟨∅, vt, A / (2 * A - β)⟩ := by sorry

end SubadditiveMMS580.Amplification.Supplement
