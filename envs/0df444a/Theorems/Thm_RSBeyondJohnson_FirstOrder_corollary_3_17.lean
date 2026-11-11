-- Prove2me | Theorems.Thm_RSBeyondJohnson_FirstOrder_corollary_3_17
-- name    : RSBeyondJohnson.FirstOrder.corollary_3_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:32:47.172927+00:00
-- url     : https://prove2.me/theorems/b4d2b89d-fca0-4d33-9d94-4b94e8ba464a
-- title:
--   Corollary 3.17 — explainer above the curve
-- statement:
--   Fix $0<\rho<a<1$ with $a>a_1(\rho)$, integers $n\ge2$, $2\le k\le\rho n$ and $an\le A\le n$, and choose $(m,B_\partial,B_{\mathrm{jet}},B_Z)$ by (28). Over every field $F$, for all distinct evaluation points $\alpha_1,\dots,\alpha_n$ and all $f,g\in F^n$, there is $Q\in F[Z]\otimes_F\mathcal V_{m,B_\partial,B_{\mathrm{jet}}}$ (the first-order support with $D=k-1$) with
--   $$\deg_ZQ\le B_Z,\qquad Q(X,z,Y)\ne0\ \text{for every }z\text{ in every extension field of }F,$$
--   such that every $P$ of degree $<k$ with $|S_z(P)|\ge A$ for the line $f+zg$ satisfies $Q(X,z,P,P^{[1]})=0$. This symbolic first-order explainer is the input of the counting in Section 5.
--
--   Differences from the source:
--   - encoding: positions 1, …, n; distinct evaluation points α_1, …, α_n → Fin n (0-based); α : Fin n → F with Function.Injective α; reason: Lean indexing; the same instances
--   - encoding: choose (m, B∂, B_jet, B_Z) by (28) → mParam, bDel, bJet, bZ ρ a n (definition Params); reason: the printed formulas of (28), as functions of (ρ, a, n) only
--   - encoding: V_{m,B∂,B_jet} with D = K − 1, K = max{k, 2} → firstOrderSupport F m B∂ B_jet (k − 1) A; reason: k ≥ 2, so K = k and D = k − 1
--   - encoding: Q ∈ F[Z] ⊗_F V; deg_Z; Q(X, z, Y) → a polynomial in Z over F[X, Y₀, Y₁] with every Z-coefficient in V; natDegree; specZ Q z; reason: same object
--   - reading: Q(X, z, Y) ≠ 0 for every z → for every field L : Type u with Algebra F L and every z : L, specZ (Q mapped to L) z ≠ 0 (z ∈ F is the case L = F); reason: the stronger of the two readings, the one the paper uses: Proposition 3.13, from which the corollary follows, states it for every z ∈ F̄ (p. 20), and p. 19 says the construction makes Q(X, z, Y) nonzero for every z over every field extension
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), p. 25, Corollary 3.17

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
import Definitions.Def_RSBeyondJohnson_FirstOrder_Agreement
import Definitions.Def_RSBeyondJohnson_FirstOrder_Interpolation
import Definitions.Def_RSBeyondJohnson_FirstOrder_Curve
import Definitions.Def_RSBeyondJohnson_FirstOrder_Params

open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-- **Corollary 3.17 (Explainer above the curve)**, p. 25. Fix `0 < ρ < a < 1` with
`a > a₁(ρ)`, integers `n ≥ 2`, `2 ≤ k ≤ ρn`, `an ≤ A ≤ n`, and `(m, B∂, B_jet, B_Z)` from (28).
Over every field, for all distinct evaluation points and all `f, g ∈ F^n`, there is
`Q ∈ F[Z] ⊗_F V_{m,B∂,B_jet}` (with `D = k − 1`) with `deg_Z Q ≤ B_Z` and `Q(X, z, Y) ≠ 0` for
every `z` — read, as in Proposition 3.13 (`z ∈ F̄`) and the remark after Definition 3.10, as every
`z` in every extension `L` of `F` (`z ∈ F` is the case `L = F`) — satisfying (17) at degree bound
`k` and threshold `A`. -/
theorem corollary_3_17.{u} (ρ a : ℝ) (hρ : 0 < ρ) (hρa : ρ < a) (ha : a < 1) (hcurve : a1 ρ < a)
    (n k A : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) (hkρ : (k : ℝ) ≤ ρ * n) (hA : a * n ≤ A)
    (hAn : A ≤ n) (F : Type u) [Field F] (α : Fin n → F) (hα : Function.Injective α)
    (f g : Fin n → F) :
    ∃ Q : (MvPolynomial (Option (Fin 2)) F)[X],
      (∀ j, Q.coeff j ∈
        firstOrderSupport F (mParam ρ a n) (bDel ρ a n) (bJet ρ a n) (k - 1) A) ∧
      Q.natDegree ≤ bZ ρ a n ∧
      (∀ (L : Type u) [Field L] [Algebra F L] (z : L),
        specZ (Q.map (MvPolynomial.map (algebraMap F L))) z ≠ 0) ∧
      ∀ z : F, ∀ P : F[X], P.degree < (k : WithBot ℕ) →
        A ≤ (agrSet α (lineCurve f g) z P).card →
        RSListDecodingCapacity.AllRates.hasseJetEval 1 (specZ Q z) P = 0 := by sorry

end RSBeyondJohnson.FirstOrder
