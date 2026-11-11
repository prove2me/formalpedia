-- Prove2me | Theorems.Thm_PolySwap_KMS_lemma_3_9
-- name    : PolySwap.KMS.lemma_3_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:41:51.838164+00:00
-- url     : https://prove2.me/theorems/1c5ddfe9-d2ab-4407-ab40-f3a5e71fd706
-- title:
--   Lemma 3.9 — vanishing cohomology: $H^1(F^{\mathcal I}X(A_d,\mathbb F_q,f),\Lambda)=1$
-- statement:
--   Let $r,d,T\in\mathbb N$ with $d,T\ge3$. For all prime powers $q=p^m\ge5$, all groups $\Lambda$ without non-trivial elements of order $p$, all irreducible polynomials $f\in\mathbb F_q[t]$ of degree $\ge2$ and all nice sets of disjoint colours $\mathcal I\in\binom{[d]}{r+1}^{[T]}$,
--   $$H^1\big(F^{\mathcal I}X(A_d,\mathbb F_q,f),\Lambda\big)=1.$$
--
--   Differences from the source:
--   - encoding: r ∈ ℕ (the paper's ℕ excludes 0: it writes ℕ₀ for {0, 1, …}, p. 9; Definitions 2.11 and 2.14 assume 1 ≤ r) → hypothesis 1 ≤ r; reason: the paper's standing convention made explicit
--   - encoding: a prime power q = p^m and the field F_q → a finite field F (Fintype F) with q = Fintype.card F and p = ringChar F; reason: every finite field has prime-power order q and prime characteristic p; same instances
--   - encoding: groups Λ without non-trivial elements of order p → any group Λ (Type*) with ∀ g, g ^ ringChar F = 1 → g = 1; reason: p is prime, so g ≠ 1 with g^p = 1 has order exactly p; same groups
--   - encoding: X(A_d, F_q, f) = CC(SL_{d+1}(F_q[t]/(f)); (π_f(U_{[d]∖{i}}))_{i∈[d]}) with the uniform top-level distribution → kmsX d F f: cosetComplex over SL (Fin (d+1)) (AdjoinRoot f) of Hf d F f i = (U d F ([d]∖{i})).map (SpecialLinearGroup.map (AdjoinRoot.mk f)), vertices ⟨i, gH^f_i⟩ : Σ i, G ⧸ H^f_i, colour i; reason: Lean convention (0-based matrix indices, F_q[t]/(f) as AdjoinRoot f); the same complex and weights
--   - encoding: H¹(Y, Λ) = 1 (every orbit of a cocycle is that of the trivial cocycle, equivalently B¹ = Z¹) → H1Trivial: every 1-cocycle equals d₀g on every ordered edge for some 0-cochain g; reason: the paper's equivalence (p. 12); cochains are total functions and only their values on the complex count
--   - reading: condition (e) of Definition 3.6: 'for every pair of J-bins B, B′' → IsNice quantifies (e) over every pair (ℓ, ℓ′) of nonempty bins, B = B′ included; empty bins are omitted, as the definition says; reason: a pair is an arbitrary pair, as the proof of Lemma 3.7 counts it (p. 34: 'This count allows the two bins to belong to arbitrary color sets, as in the definition'); reading it as two different bins would weaken Lemma 3.7
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), Lemma 3.9, p. 25

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Cohomology
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_KMSComplex

open Polynomial

namespace PolySwap.KMS

/-- **Lemma 3.9**, p. 25. Let `r, d, T ∈ ℕ`, `d, T ≥ 3`. For all prime powers `q = p^m ≥ 5`, all
groups `Λ` without non-trivial elements of order `p`, all irreducible `f ∈ F_q[t]` of degree
`≥ 2` and all nice sets `I` of `T` disjoint colour sets, `H¹(F^I X(A_d, F_q, f), Λ) = 1`. -/
theorem lemma_3_9 (r d T : ℕ) (hr : 1 ≤ r) (hd : 3 ≤ d) (hT : 3 ≤ T)
    (F : Type*) [Field F] [Fintype F] (hq : 5 ≤ Fintype.card F)
    (Λ : Type*) [Group Λ] (hΛ : ∀ g : Λ, g ^ ringChar F = 1 → g = 1)
    (f : F[X]) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (I : Finset (Finset ℕ)) (hI : I ∈ disjointColorSets d r T) (hnice : IsNice d I) :
    (kmsFI d F f I).H1Trivial Λ := by sorry

end PolySwap.KMS
