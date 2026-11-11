-- Prove2me | Theorems.Thm_RSBeyondJohnson_FirstOrder_lemma_4_1
-- name    : RSBeyondJohnson.FirstOrder.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:32:29.538501+00:00
-- url     : https://prove2.me/theorems/39553469-8025-467c-88ff-e360c36f6915
-- title:
--   Lemma 4.1 — dimension-sensitive agreement incidence
-- statement:
--   Work over an algebraically closed field $E$ with distinct evaluation points $\alpha_1,\dots,\alpha_n$.
--   (1) In the coefficient space $E^k$ of degree-$<k$ polynomials, an algebraic set of dimension at most $r$ and total degree at most $B$ has finitely many, and at most $B\,\Pi_r(T)$, points agreeing with a fixed word in at least $T$ positions ($k\le T\le n$).
--   (2) Let $k\le L\le A\le n$. In the joint space $\mathcal L_1$ of pairs $(z,P)$, and more generally on the lifted locus $\mathcal L_\ell$ for every $\ell\ge1$, exclude the witness graphs with at least $L$ common agreements. For an algebraic set of dimension at most $r+1$ and total degree at most $B$, the number of remaining points with at least $A$ agreements is finite and at most
--   $$B\,\frac{n-L+1}{A-L+1}\,\Pi_r(A).$$
--   Here dimension and total degree are those of `RSCapacity_AffineGeometry` (Krull dimension; sum of the Heintz degrees of the irreducible components).
--
--   Differences from the source:
--   - generalization: evaluation points in the base field F and words over F (the setting of §4.1, inside an algebraically closed E) → α : Fin n → E injective and words y, w over E; reason: the paper's points and words are their images in E, a special case
--   - encoding: coefficient space; L_ℓ; agreement hyperplanes; witness graphs with ≥ L common agreements → Fin k → E; liftedLocus E ℓ k ⊆ Fin (ℓ + k) → E; liftAgrCount; highWitnessGraphs (Geometry); reason: coordinates as on p. 26; L₁ is the case ℓ = 1
--   - encoding: algebraic set of dimension at most r and total degree at most B → RSCapacity.IsAlgSet V, algDim V ≤ r, cdeg V ≤ B (published RSCapacity_AffineGeometry); reason: Krull dimension and Heintz's degree (the paper cites [Hei83])
--   - encoding: has at most N points → the set is Finite and its ncard ≤ N; reason: ncard of an infinite set is 0
--   - encoding: T positions (Π_r(T) defined for k ≤ T ≤ n) → hypotheses k ≤ T ≤ n; reason: the domain of (31)
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), p. 26, Lemma 4.1

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
import Definitions.Def_RSCapacity_AffineGeometry
import Definitions.Def_RSBeyondJohnson_FirstOrder_Agreement
import Definitions.Def_RSBeyondJohnson_FirstOrder_Counting
import Definitions.Def_RSBeyondJohnson_FirstOrder_Geometry

open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-- **Lemma 4.1 (Dimension-sensitive agreement incidence)**, p. 26, over an algebraically closed
field `E` with distinct evaluation points `α_i ∈ E`.
(1) In the coefficient space `E^k` of degree-`< k` polynomials, an algebraic set `V` of dimension
at most `r` and total degree at most `B` has at most `B Π_r(T)` points (finitely many) agreeing
with a fixed word `y` in at least `T` positions, for every `k ≤ T ≤ n`.
(2) For `k ≤ L ≤ A ≤ n` and every `ℓ ≥ 1` (`ℓ = 1`: the joint space `L₁` of pairs `(z, P)`), an
algebraic set `V ⊆ L_ℓ` of dimension at most `r + 1` and total degree at most `B` has at most
`B ((n − L + 1)/(A − L + 1)) Π_r(A)` points (finitely many) with at least `A` agreements outside
the witness graphs with at least `L` common agreements. -/
theorem lemma_4_1 {E : Type*} [Field E] [IsAlgClosed E] {n : ℕ} (k : ℕ) (α : Fin n → E)
    (hα : Function.Injective α) :
    (∀ (r B : ℕ) (V : Set (Fin k → E)), RSCapacity.IsAlgSet V →
      RSCapacity.algDim V ≤ ((r : ℕ∞) : WithBot ℕ∞) → RSCapacity.cdeg V ≤ (B : ℕ∞) →
      ∀ (y : Fin n → E) (T : ℕ), k ≤ T → T ≤ n →
        {p ∈ V | T ≤ RSListDecodingCapacity.AllRates.agreement α y (coeffPoly p)}.Finite ∧
        ({p ∈ V | T ≤ RSListDecodingCapacity.AllRates.agreement α y (coeffPoly p)}.ncard : ℝ) ≤
          B * incidenceFactor n k r T) ∧
    (∀ (ℓ : ℕ), 1 ≤ ℓ → ∀ (L A r B : ℕ), k ≤ L → L ≤ A → A ≤ n →
      ∀ (w : Fin (ℓ + 1) → Fin n → E) (V : Set (Fin (ℓ + k) → E)), RSCapacity.IsAlgSet V →
        V ⊆ liftedLocus E ℓ k →
        RSCapacity.algDim V ≤ (((r + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) → RSCapacity.cdeg V ≤ (B : ℕ∞) →
        {x ∈ V \ highWitnessGraphs ℓ k L α w | A ≤ liftAgrCount α w x}.Finite ∧
        ({x ∈ V \ highWitnessGraphs ℓ k L α w | A ≤ liftAgrCount α w x}.ncard : ℝ) ≤
          B * (((n : ℝ) - L + 1) / ((A : ℝ) - L + 1)) * incidenceFactor n k r A) := by sorry

end RSBeyondJohnson.FirstOrder
