-- Prove2me | Theorems.Thm_RSBeyondJohnson_FirstOrder_lemma_4_2
-- name    : RSBeyondJohnson.FirstOrder.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:32:39.822512+00:00
-- url     : https://prove2.me/theorems/d9a43790-fba9-4d91-be93-4869fc84baf3
-- title:
--   Lemma 4.2 — geometric transfer on a polynomial received curve
-- statement:
--   Let $F$ be a field, $E$ an algebraically closed extension, $1\le k\le L\le A\le n$, $\ell\ge1$, distinct $\alpha_1,\dots,\alpha_n\in F$ and words $w_0,\dots,w_\ell\in F^n$. Let $V_1,\dots,V_N\subseteq\mathcal L_\ell$ be closed algebraic sets over $E$ with $\dim V_\nu\le r_\nu+1$ and total degree at most $J_\nu$. Let $z^*$ be transcendental over $E$, and suppose the reduced fiber of $V_\nu$ over $z^*$, after base change to an algebraic closure of $E(z^*)$, has dimension at most $r_\nu$ and total degree at most $F_\nu$. Let $\mathcal C$ be a collection of pairs $(z,P)$ with $z\in F$ and $\deg P<k$ such that, outside a finite preliminary set $\mathcal E_{\mathrm{pre}}\subseteq F$, every $(z,P)\in\mathcal C$ gives a point $(z,z^2,\dots,z^\ell,P)\in\bigcup_\nu V_\nu$. Then there is $\mathcal E\subseteq F$ of size at most
--   $$|\mathcal E_{\mathrm{pre}}|+\frac{n-L+1}{A-L+1}\sum_\nu\Pi_{r_\nu}(A)J_\nu+\ell(n-L)\sum_\nu\Pi_{r_\nu}(L)F_\nu\qquad(32)$$
--   such that every $(z,P)\in\mathcal C$ with $z\notin\mathcal E$ and at least $A$ agreements with $w(z)$ admits $P_0,\dots,P_\ell\in F[X]$ of degree $<k$ with $P=\sum_tz^tP_t$ and $S_z(P)=S(P_0,\dots,P_\ell)$.
--
--   Differences from the source:
--   - encoding: positions 1, …, n; distinct evaluation points α_1, …, α_n → Fin n (0-based); α : Fin n → F with Function.Injective α; reason: Lean indexing; the same instances
--   - encoding: z* transcendental over E; base change to an algebraic closure of E(z*); reduced fiber → z* = RatFunc.X in AlgebraicClosure (RatFunc E); genericFiber E ℓ k V (points p with (z*, …, z*^ℓ, p) a zero of every polynomial vanishing on V); reason: any transcendental gives an isomorphic fiber; a set of points is reduced
--   - encoding: J_ν, F_ν numbers bounding total degree → J ν, Fν ν : ℝ with cdeg ≠ ⊤ and its value ≤ J ν (resp. Fν ν); reason: cdeg is ℕ∞-valued
--   - encoding: dimension and total degree of algebraic sets → algDim, cdeg, IsAlgSet of the published RSCapacity_AffineGeometry; reason: Krull dimension; sum of Heintz degrees of components
--   - encoding: collection C, finite E_pre, E ⊆ F of size at most (32) → C : Set (F × F[X]); Epre, Ex : Finset F; reason: finite sets of challenges
--   - encoding: the conclusion for (z, P) → HasFullCommonWitness k α w z P; reason: Definition 3.1, the same two equalities
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), pp. 27–28, Lemma 4.2

import Mathlib
import Definitions.Def_RSCapacity_AffineGeometry
import Definitions.Def_RSBeyondJohnson_FirstOrder_Agreement
import Definitions.Def_RSBeyondJohnson_FirstOrder_Counting
import Definitions.Def_RSBeyondJohnson_FirstOrder_Geometry

open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-- **Lemma 4.2 (Geometric transfer on a polynomial received curve)**, pp. 27–28. Let `F` be a
field, `E` an algebraically closed extension, `1 ≤ k ≤ L ≤ A ≤ n`, `ℓ ≥ 1`, distinct
`α_i ∈ F`, words `w_0, …, w_ℓ ∈ F^n`. Let `V_1, …, V_N ⊆ L_ℓ` be closed algebraic sets over `E`
with `dim V_ν ≤ r_ν + 1` and total degree `≤ J_ν`. Let `z*` be transcendental over `E` and suppose the
reduced fiber of `V_ν` over `z*`, after base change to an algebraic closure of `E(z*)`
(`genericFiber`), has dimension `≤ r_ν` and total degree `≤ F_ν`. Let `C` be pairs `(z, P)`,
`z ∈ F`, `deg P < k`, such that outside a finite `E_pre ⊆ F` every `(z, P) ∈ C` gives a point
`(z, …, z^ℓ, P) ∈ ⋃_ν V_ν`. Then there is `E ⊆ F` of size at most (32)
`|E_pre| + ((n − L + 1)/(A − L + 1)) ∑_ν Π_{r_ν}(A) J_ν + ℓ(n − L) ∑_ν Π_{r_ν}(L) F_ν` such that
every `(z, P) ∈ C` with `z ∉ E` and at least `A` agreements with `w(z)` has the full
common-witness property (witnesses of degree `< k` over `F`). -/
theorem lemma_4_2 {F : Type*} [Field F] (E : Type*) [Field E] [IsAlgClosed E] [Algebra F E]
    {n : ℕ} (k L A ℓ : ℕ) (hk : 1 ≤ k) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n) (hℓ : 1 ≤ ℓ)
    (α : Fin n → F) (hα : Function.Injective α) (w : Fin (ℓ + 1) → Fin n → F)
    {N : ℕ} (V : Fin N → Set (Fin (ℓ + k) → E)) (hValg : ∀ ν, RSCapacity.IsAlgSet (V ν))
    (hVL : ∀ ν, V ν ⊆ liftedLocus E ℓ k) (r : Fin N → ℕ) (J Fν : Fin N → ℝ)
    (hdim : ∀ ν, RSCapacity.algDim (V ν) ≤ (((r ν + 1 : ℕ) : ℕ∞) : WithBot ℕ∞))
    (hdeg : ∀ ν, RSCapacity.cdeg (V ν) ≠ ⊤ ∧ ((RSCapacity.cdeg (V ν)).toNat : ℝ) ≤ J ν)
    (hfibdim : ∀ ν, RSCapacity.algDim (genericFiber E ℓ k (V ν)) ≤ ((r ν : ℕ∞) : WithBot ℕ∞))
    (hfibdeg : ∀ ν, RSCapacity.cdeg (genericFiber E ℓ k (V ν)) ≠ ⊤ ∧
      ((RSCapacity.cdeg (genericFiber E ℓ k (V ν))).toNat : ℝ) ≤ Fν ν)
    (C : Set (F × F[X])) (hCdeg : ∀ c ∈ C, c.2.degree < (k : WithBot ℕ))
    (Epre : Finset F)
    (hC : ∀ c ∈ C, c.1 ∉ Epre →
      liftPoint ℓ k (algebraMap F E c.1) (fun j : Fin k => algebraMap F E (c.2.coeff j)) ∈
        ⋃ ν, V ν) :
    ∃ Ex : Finset F,
      (Ex.card : ℝ) ≤ (Epre.card : ℝ) +
        ((n : ℝ) - L + 1) / ((A : ℝ) - L + 1) * ∑ ν, incidenceFactor n k (r ν) A * J ν +
        (ℓ : ℝ) * ((n : ℝ) - L) * ∑ ν, incidenceFactor n k (r ν) L * Fν ν ∧
      ∀ c ∈ C, c.1 ∉ Ex → A ≤ (agrSet α w c.1 c.2).card →
        HasFullCommonWitness k α w c.1 c.2 := by sorry

end RSBeyondJohnson.FirstOrder
