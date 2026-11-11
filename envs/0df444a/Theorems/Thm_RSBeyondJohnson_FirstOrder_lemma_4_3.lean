-- Prove2me | Theorems.Thm_RSBeyondJohnson_FirstOrder_lemma_4_3
-- name    : RSBeyondJohnson.FirstOrder.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:32:18.767422+00:00
-- url     : https://prove2.me/theorems/416c0e7c-7ed0-46e2-943b-400e5986a8e9
-- title:
--   Lemma 4.3 — ordinary MCA transfer in every characteristic
-- statement:
--   Let $F$ be any field, $1\le D\le n-2$, $D+1\le L\le A\le n$, distinct $\alpha_1,\dots,\alpha_n\in F$, and a received curve $w(Z)=\sum_{t=0}^\ell Z^tw_t$ with $\ell\ge1$. Suppose the nonzero polynomial $Q\in F[X,Z,Y]$ satisfies $\deg_YQ\le B_{\mathrm{jet}}$, $\deg_ZQ\le B_Z$, $B_{\mathrm{jet}}\ge1$. Then there is a set $\mathcal E_Q\subseteq F$ of size at most
--   $$E^{(\ell)}_{\mathrm{ord}}(D,A,n;B_{\mathrm{jet}},B_Z;L)\qquad(35)$$
--   such that every $z\notin\mathcal E_Q$ and every $P$ of degree $\le D$ with $Q(X,z,P(X))=0$ and $|S_z(P)|\ge A$ has the full common-witness property with message dimension $D+1$. No restriction on the characteristic is needed.
--
--   Differences from the source:
--   - encoding: positions 1, …, n; distinct evaluation points α_1, …, α_n → Fin n (0-based); α : Fin n → F with Function.Injective α; reason: Lean indexing; the same instances
--   - encoding: Q ∈ F[X, Z, Y]; deg_Y Q; deg_Z Q; Q(X, z, P(X)) → a polynomial in Z over MvPolynomial (Option (Fin 1)) F; degreeOf Y of every Z-coefficient; natDegree; hasseJetEval 0 (specZ Q z) P; reason: same object; with d = 0 the substitution is Q(X, P)
--   - encoding: 1 ≤ D ≤ n − 2; P ∈ F[X]_{≤D} → 1 ≤ D, D + 2 ≤ n; P.natDegree ≤ D; reason: avoids natural subtraction; zero polynomial included
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), pp. 28–29, Lemma 4.3

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
import Definitions.Def_RSBeyondJohnson_FirstOrder_Agreement
import Definitions.Def_RSBeyondJohnson_FirstOrder_Interpolation
import Definitions.Def_RSBeyondJohnson_FirstOrder_Counting

open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-- **Lemma 4.3 (Ordinary MCA transfer in every characteristic)**, pp. 28–29. Let `F` be any
field, `1 ≤ D ≤ n − 2`, `D + 1 ≤ L ≤ A ≤ n`, distinct `α_1, …, α_n ∈ F`, and a received curve
`w(Z) = ∑_{t=0}^{ℓ} Z^t w_t` with `ℓ ≥ 1`. If the nonzero `Q ∈ F[X, Z, Y]` has
`deg_Y Q ≤ B_jet`, `deg_Z Q ≤ B_Z` and `B_jet ≥ 1`, there is `E_Q ⊆ F` with
`|E_Q| ≤ E^(ℓ)_ord(D, A, n; B_jet, B_Z; L)` (35) such that every `z ∉ E_Q` and every
`P ∈ F[X]_{≤D}` with `Q(X, z, P(X)) = 0` and `|S_z(P)| ≥ A` has the full common-witness property
with message dimension `D + 1`. `F[X, Z, Y]` is `(MvPolynomial (Option (Fin 1)) F)[X]` (`Z`
outer, `none = X`, `some 0 = Y`). -/
theorem lemma_4_3 {F : Type*} [Field F] {n ℓ : ℕ} (D L A Bjet BZ : ℕ) (hD : 1 ≤ D)
    (hDn : D + 2 ≤ n) (hL : D + 1 ≤ L) (hLA : L ≤ A) (hAn : A ≤ n) (hℓ : 1 ≤ ℓ)
    (α : Fin n → F) (hα : Function.Injective α) (w : Fin (ℓ + 1) → Fin n → F)
    (Q : (MvPolynomial (Option (Fin 1)) F)[X]) (hQ : Q ≠ 0)
    (hY : ∀ j, (Q.coeff j).degreeOf (some 0) ≤ Bjet) (hZ : Q.natDegree ≤ BZ) (hB : 1 ≤ Bjet) :
    ∃ EQ : Finset F, (EQ.card : ℝ) ≤ eOrd ℓ D A n Bjet BZ L ∧
      ∀ z : F, z ∉ EQ → ∀ P : F[X], P.natDegree ≤ D →
        RSListDecodingCapacity.AllRates.hasseJetEval 0 (specZ Q z) P = 0 →
        A ≤ (agrSet α w z P).card → HasFullCommonWitness (D + 1) α w z P := by sorry

end RSBeyondJohnson.FirstOrder
