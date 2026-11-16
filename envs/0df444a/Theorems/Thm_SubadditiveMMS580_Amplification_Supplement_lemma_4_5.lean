-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_Supplement_lemma_4_5
-- name    : SubadditiveMMS580.Amplification.Supplement.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:57:01.627531+00:00
-- url     : https://prove2.me/theorems/b1c10641-1a63-49f4-b3b1-b541e661387e
-- title:
--   Lemma 4.5 — from aggregate value losses to potential losses
-- statement:
--   Let $\alpha>0$ and let $f:[0,\infty)\to[0,\infty)$ be nondecreasing, zero on $[0,\alpha]$ and concave on $[\alpha,\infty)$. Suppose that
--   $$f(x)\le1-\frac{\alpha}{x}\quad(\alpha<x\le2\alpha),\qquad 2f(x)-f(x-\alpha)\le1\quad(x\ge2\alpha).\tag{13}$$
--
--   1. Let $v$ be a normalized monotone valuation on a finite set $M$ and $L\ge0$ an integer. For every $S\subseteq M$ and pairwise disjoint $B_1,\dots,B_L\subseteq S$ with
--   $$\sum_{\ell=1}^L\big[v(S)-v(S\setminus B_\ell)\big]\le v(S)$$
--   we have
--   $$\sum_{\ell=1}^L\big[f(v(S))-f(v(S\setminus B_\ell))\big]\le1.$$
--   2. In particular, the last conclusion holds for every $v\in\mathcal Q_q$ ($q\ge2$), every $L\le q$ and all pairwise disjoint $B_1,\dots,B_L\subseteq S$, without the aggregate hypothesis.
--
--   With the potential $\psi_\alpha$ of (9) this yields the donor-loss bound (11) used in Proposition 4.4.
--
--   Differences from the source:
--   - encoding: f : [0,∞) → [0,∞) → f : ℝ → ℝ, nonnegative, monotone, zero and concave only on the stated subsets of [0,∞); reason: f is only evaluated at values of v, which are nonnegative; its values on negative reals are irrelevant
--   - encoding: v : 2^M → ℝ≥0 normalized and monotone → a real set function with IsNormalized and IsMonotone; reason: these imply nonnegativity, so the instances are the same
--   - encoding: partitions $(C_1,\dots,C_t)\in\Pi(S,t)$ into $t\le q$ nonempty groups (Definition 2.1) → 1 ≤ t ≤ q and C : Fin t → Finset (Fin m) with nonempty, pairwise disjoint members whose union is S; reason: the same ordered partitions
-- source:
--   Bo Li, Ankang Sun, Toward Constant-Factor Maximin Share Guarantees for Subadditive Valuations, STOC 2027 submission #580 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/580.pdf, sha256 7de124b5706e9e49301a281a1eb418a8ae32d04bf4cf0941b969cc3cde85e485, Lemma 4.5, p. 28 (PDF p. 28)

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Supplement_Partitioning
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_LittleCharity_MMS_Setting

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Supplement

/-- Lemma 4.5 (Li–Sun, STOC 2027 submission #580, p. 28): let `α > 0` and let `f`, on `[0, ∞)`,
be nonnegative, nondecreasing, zero on `[0, α]` and concave on `[α, ∞)`, with
`f(x) ≤ 1 − α/x` for `α < x ≤ 2α` and `2f(x) − f(x − α) ≤ 1` for `x ≥ 2α` (13). Then for every
normalized monotone `v`, every `L ≥ 0` and pairwise disjoint `B_1, …, B_L ⊆ S` with
`∑_ℓ [v(S) − v(S \ B_ℓ)] ≤ v(S)`, `∑_ℓ [f(v(S)) − f(v(S \ B_ℓ))] ≤ 1`; in particular this
holds for `v ∈ Q_q` and `L ≤ q` without the aggregate hypothesis. -/
theorem lemma_4_5 (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ)
    (hnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x) (hmono : MonotoneOn f (Set.Ici 0))
    (hzero : ∀ x ∈ Set.Icc 0 α, f x = 0) (hconc : ConcaveOn ℝ (Set.Ici α) f)
    (h13a : ∀ x : ℝ, α < x → x ≤ 2 * α → f x ≤ 1 - α / x)
    (h13b : ∀ x : ℝ, 2 * α ≤ x → 2 * f x - f (x - α) ≤ 1) :
    (∀ {m : ℕ} (v : Finset (Fin m) → ℝ), IsNormalized v → IsMonotone v →
      ∀ (L : ℕ) (S : Finset (Fin m)) (B : Fin L → Finset (Fin m)),
        (∀ k l : Fin L, k ≠ l → Disjoint (B k) (B l)) → (∀ l, B l ⊆ S) →
        ∑ l : Fin L, (v S - v (S \ B l)) ≤ v S →
        ∑ l : Fin L, (f (v S) - f (v (S \ B l))) ≤ 1) ∧
    (∀ {m : ℕ} (q : ℕ), 2 ≤ q → ∀ v : Finset (Fin m) → ℝ, IsQPartitioning q v →
      ∀ (L : ℕ), L ≤ q → ∀ (S : Finset (Fin m)) (B : Fin L → Finset (Fin m)),
        (∀ k l : Fin L, k ≠ l → Disjoint (B k) (B l)) → (∀ l, B l ⊆ S) →
        ∑ l : Fin L, (f (v S) - f (v (S \ B l))) ≤ 1) := by sorry

end SubadditiveMMS580.Amplification.Supplement
