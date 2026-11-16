-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_Supplement_lemma_4_2
-- name    : SubadditiveMMS580.Amplification.Supplement.lemma_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T19:55:09.381212+00:00
-- url     : https://prove2.me/theorems/5b47ab0e-6b2b-4a68-bc25-7b504692db04
-- title:
--   Lemma 4.2 — disjoint deletion losses of a $q$-partitioning valuation are at most $\max\{1,L/q\}f(S)$
-- statement:
--   Let $q\ge2$, let $f\in\mathcal Q_q$, let $L\ge0$ be an integer, and let $B_1,\dots,B_L$ be pairwise disjoint (possibly empty) subsets of a set $S\subseteq M$. Then
--   $$\sum_{\ell=1}^{L}\big(f(S)-f(S\setminus B_\ell)\big)\le\max\{1,L/q\}\,f(S).$$
--
--   The bound controls the total loss a donor suffers over separately evaluated transfers in the proofs of Propositions 4.3 and 4.4.
--
--   Differences from the source:
--   - encoding: partitions $(C_1,\dots,C_t)\in\Pi(S,t)$ into $t\le q$ nonempty groups (Definition 2.1) → 1 ≤ t ≤ q and C : Fin t → Finset (Fin m) with nonempty, pairwise disjoint members whose union is S; reason: the same ordered partitions
--   - encoding: valuations $v_i : 2^M \to \mathbb R_{\ge 0}$, normalized and monotone → real set functions on Finset (Fin m) with the published IsNormalized and IsMonotone predicates; reason: normalization and monotonicity give nonnegativity, so the instances are the same
-- source:
--   Bo Li, Ankang Sun, Toward Constant-Factor Maximin Share Guarantees for Subadditive Valuations, STOC 2027 submission #580 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/580.pdf, sha256 7de124b5706e9e49301a281a1eb418a8ae32d04bf4cf0941b969cc3cde85e485, Lemma 4.2, p. 21 (PDF p. 21)

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Supplement_Partitioning
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_LittleCharity_MMS_Setting

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Supplement

/-- Lemma 4.2 (Li–Sun, STOC 2027 submission #580, p. 21): for an integer `L ≥ 0`, `f ∈ Q_q`
(`q ≥ 2`) and pairwise disjoint subsets `B_1, …, B_L` of a set `S ⊆ M`,
`∑_ℓ (f(S) − f(S \ B_ℓ)) ≤ max {1, L/q} · f(S)`. -/
theorem lemma_4_2 {m : ℕ} (q : ℕ) (hq : 2 ≤ q) (f : Finset (Fin m) → ℝ)
    (hf : IsQPartitioning q f) (L : ℕ) (S : Finset (Fin m)) (B : Fin L → Finset (Fin m))
    (hdisj : ∀ k l : Fin L, k ≠ l → Disjoint (B k) (B l)) (hsub : ∀ l, B l ⊆ S) :
    ∑ l : Fin L, (f S - f (S \ B l)) ≤ max 1 ((L : ℝ) / q) * f S := by sorry

end SubadditiveMMS580.Amplification.Supplement
