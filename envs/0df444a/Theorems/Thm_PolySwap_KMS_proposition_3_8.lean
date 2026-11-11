-- Prove2me | Theorems.Thm_PolySwap_KMS_proposition_3_8
-- name    : PolySwap.KMS.proposition_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:41:31.856246+00:00
-- url     : https://prove2.me/theorems/c5c8121b-326d-4b1f-b922-ebb180772be2
-- title:
--   Proposition 3.8 — nice colored faces complexes are coboundary expanders: $h^1(F^{\mathcal I}X,\Lambda)\ge\beta_1$ and $H^1=1$
-- statement:
--   Let $r,T,d\in\mathbb N$ such that $T\ge4$ and $(r+1)T\le d+1$. There exist $\beta_1>0$ and $q_0\in\mathbb N$ such that for all prime powers $q=p^m\ge q_0$, all groups $\Lambda$ without non-trivial elements of order $p$, all irreducible polynomials $f\in\mathbb F_q[t]$ of degree $\ge2$ and all nice sets of $T$ disjoint colours $\mathcal I\in\binom{[d]}{r+1}^{[T]}$,
--   $$h^1(F^{\mathcal I}X,\Lambda)\ge\beta_1\quad\text{and}\quad H^1(F^{\mathcal I}X,\Lambda)=1,$$
--   where $X=X(A_d,\mathbb F_q,f)$.
--
--   Differences from the source:
--   - encoding: r ∈ ℕ (the paper's ℕ excludes 0: it writes ℕ₀ for {0, 1, …}, p. 9; Definitions 2.11 and 2.14 assume 1 ≤ r) → hypothesis 1 ≤ r; reason: the paper's standing convention made explicit
--   - encoding: a prime power q = p^m and the field F_q → a finite field F (Fintype F) with q = Fintype.card F and p = ringChar F; reason: every finite field has prime-power order q and prime characteristic p; same instances
--   - encoding: groups Λ without non-trivial elements of order p → any group Λ (Type*) with ∀ g, g ^ ringChar F = 1 → g = 1; reason: p is prime, so g ≠ 1 with g^p = 1 has order exactly p; same groups
--   - encoding: X(A_d, F_q, f) = CC(SL_{d+1}(F_q[t]/(f)); (π_f(U_{[d]∖{i}}))_{i∈[d]}) with the uniform top-level distribution → kmsX d F f: cosetComplex over SL (Fin (d+1)) (AdjoinRoot f) of Hf d F f i = (U d F ([d]∖{i})).map (SpecialLinearGroup.map (AdjoinRoot.mk f)), vertices ⟨i, gH^f_i⟩ : Σ i, G ⧸ H^f_i, colour i; reason: Lean convention (0-based matrix indices, F_q[t]/(f) as AdjoinRoot f); the same complex and weights
--   - encoding: h¹(Y, Λ) ≥ β with h¹ the minimum ratio ‖d₁ϕ‖ / min_{ψ∈Z¹} dist(ϕ, ψ) over ϕ ∉ Z¹ (Definition 2.8) → HOneGe: every 1-cochain ϕ has a 1-cocycle ψ with β · dist(ϕ, ψ) ≤ ‖d₁ϕ‖; reason: equivalent on a finite complex with positive Garland weights: the minimum distance to Z¹ is attained and positive for ϕ ∉ Z¹, and ϕ ∈ Z¹ takes ψ = ϕ
--   - encoding: H¹(Y, Λ) = 1 (every orbit of a cocycle is that of the trivial cocycle, equivalently B¹ = Z¹) → H1Trivial: every 1-cocycle equals d₀g on every ordered edge for some 0-cochain g; reason: the paper's equivalence (p. 12); cochains are total functions and only their values on the complex count
--   - reading: condition (e) of Definition 3.6: 'for every pair of J-bins B, B′' → IsNice quantifies (e) over every pair (ℓ, ℓ′) of nonempty bins, B = B′ included; empty bins are omitted, as the definition says; reason: a pair is an arbitrary pair, as the proof of Lemma 3.7 counts it (p. 34: 'This count allows the two bins to belong to arbitrary color sets, as in the definition'); reading it as two different bins would weaken Lemma 3.7
--   - encoding: β₁ > 0 and q₀ depending on (r, T, d) → ∃ β₁ > 0, ∃ q₀ : ℕ after r, T, d and before F : Type u, Λ : Type v; reason: quantifier order as printed; Lean fixes one universe for F and one for Λ
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), Proposition 3.8, p. 24

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Cohomology
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_KMSComplex

open Polynomial

universe u v

namespace PolySwap.KMS

/-- **Proposition 3.8**, p. 24. Let `r, T, d ∈ ℕ` with `T ≥ 4` and `(r + 1)T ≤ d + 1`. There exist
`β₁ > 0` and `q₀ ∈ ℕ` such that for all prime powers `q = p^m ≥ q₀`, all groups `Λ` without
non-trivial elements of order `p`, all irreducible `f ∈ F_q[t]` of degree `≥ 2` and all nice sets
`I` of `T` disjoint colour sets, `h¹(F^I X, Λ) ≥ β₁` and `H¹(F^I X, Λ) = 1`, where
`X = X(A_d, F_q, f)`. -/
theorem proposition_3_8 (r T d : ℕ) (hr : 1 ≤ r) (hT : 4 ≤ T) (hrT : (r + 1) * T ≤ d + 1) :
    ∃ β₁ : ℝ, 0 < β₁ ∧ ∃ q₀ : ℕ, ∀ (F : Type u) [Field F] [Fintype F], q₀ ≤ Fintype.card F →
      ∀ (Λ : Type v) [Group Λ], (∀ g : Λ, g ^ ringChar F = 1 → g = 1) →
      ∀ f : F[X], Irreducible f → 2 ≤ f.natDegree →
      ∀ I ∈ disjointColorSets d r T, IsNice d I →
        (kmsFI d F f I).HOneGe Λ β₁ ∧ (kmsFI d F f I).H1Trivial Λ := by sorry

end PolySwap.KMS
