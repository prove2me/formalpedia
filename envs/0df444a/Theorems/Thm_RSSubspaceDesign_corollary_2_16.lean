-- Prove2me | Theorems.Thm_RSSubspaceDesign_corollary_2_16
-- name    : RSSubspaceDesign.corollary_2_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:25:39.53191+00:00
-- url     : https://prove2.me/theorems/410b8161-69b4-43d2-827c-6a5f3491dc21
-- title:
--   Corollary 2.16 — a reduced $K[X]$-basis of $A\cap F[X]$ for a $K(X)$-subspace $A\subseteq F(X)$
-- statement:
--   Let $K\subseteq F$ be finite fields, $L=K(X)$, and $A\subseteq F(X)$ an $L$-linear space of dimension $d$. Set
--   $$M=A\cap F[X],\qquad M_k=A\cap F[X]_{<k}\quad(k\in\mathbb Z_{\ge0}).$$
--   Then $M$ has rank $d$ over $K[X]$ and has a reduced $K[X]$-basis $a_1(X),\dots,a_d(X)$ with respect to ordinary polynomial degree: for all $c_1,\dots,c_d\in K[X]$,
--   $$\deg\Big(\sum_i c_i a_i\Big)=\max_i(\deg a_i+\deg c_i).\qquad(2.1)$$
--   In particular, for every integer $k\ge0$,
--   $$M_k=\Big\{\sum_{i=1}^d a_i(X)c_i(X)\ :\ c_i(X)\in K[X]_{<k-\deg a_i}\Big\}.$$
--
--   Here $\deg0=-\infty$, $\max\emptyset=-\infty$ and $K[X]_{<m}=\{0\}$ for $m\le0$. Proposition 4.3 applies this to the $K(X)$-span of a polynomial space $W$.
--
--   Differences from the source:
--   - encoding: F(X) as a K(X)-vector space → RatFunc F with the K(X)-algebra structure ratFuncAlgebra (coefficient map, X ↦ X); F[X] ⊆ F(X) by algebraMap; reason: this is the standard inclusion K(X) ⊆ F(X)
--   - encoding: M has rank d over K[X] and has a reduced K[X]-basis a₁, …, a_d → a₁, …, a_d ∈ M that are K[X]-linearly independent, span M over K[X] and satisfy (2.1); K[X] acts on F[X] by c · u = c.map(K → F) * u; reason: a K[X]-basis with d elements is exactly this, and it gives rank d
--   - encoding: deg with deg 0 = −∞ and max ∅ = −∞ → Polynomial.degree in WithBot ℕ and Finset.sup; reason: the same conventions
--   - encoding: cᵢ ∈ K[X]_{<k − deg aᵢ} (K[X]_{<m} = {0} for m ≤ 0) → deg cᵢ + deg aᵢ < k; reason: aᵢ ≠ 0, so both conditions hold for exactly the same cᵢ
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Corollary 2.16, p.14 (PDF p.16), with display (2.1) and the conventions of p.13 (PDF p.15)

import Mathlib
import Definitions.Def_RSSubspaceDesign_ratFuncAlgebra

open Polynomial

namespace RSSubspaceDesign

/-- **Corollary 2.16.** Alrabiah–Goyal–Guruswami, arXiv:2610.36215 (held version, sha256
cf26424b…f36206), Corollary 2.16, p.14 (with the conventions of Section 2.2, p.13).

Let `K ⊆ F` be finite fields, `L = K(X)`, and `A ⊆ F(X)` an `L`-linear space of dimension `d`. Set
`M = A ∩ F[X]` and `M_k = A ∩ F[X]_{<k}`. Then `M` has rank `d` over `K[X]` and has a reduced
`K[X]`-basis `a₁, …, a_d`, i.e. `deg(∑ cᵢ aᵢ) = maxᵢ (deg aᵢ + deg cᵢ)` for all `cᵢ ∈ K[X]`
(display (2.1)). In particular, for every `k ≥ 0`,
`M_k = {∑ aᵢ cᵢ | cᵢ ∈ K[X]_{<k − deg aᵢ}}`.

**Formalization Note.** `F(X)` is a `K(X)`-space through `ratFuncAlgebra K F`; `F[X]` sits in it by
`algebraMap F[X] (RatFunc F)`. `K[X]` acts on `F[X]` by `c • u = c.map (algebraMap K F) * u`.
"Rank `d` with a basis `a₁, …, a_d`" is stated as: the `aᵢ` lie in `M`, are `K[X]`-linearly
independent and span `M` over `K[X]`. Degrees are `Polynomial.degree` in `WithBot ℕ`, so
`deg 0 = ⊥ = −∞` and the max over an empty index set is `⊥`, as on p.13.
`cᵢ ∈ K[X]_{<k − deg aᵢ}` (with `K[X]_{<m} = {0}` for `m ≤ 0`) is written
`deg cᵢ + deg aᵢ < k`. -/
theorem corollary_2_16 {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F] (d : ℕ) :
    letI := ratFuncAlgebra K F
    ∀ A : Submodule (RatFunc K) (RatFunc F), Module.finrank (RatFunc K) A = d →
      ∃ a : Fin d → F[X],
        (∀ i, algebraMap F[X] (RatFunc F) (a i) ∈ A) ∧
        (∀ c : Fin d → K[X], ∑ i, (c i).map (algebraMap K F) * a i = 0 → c = 0) ∧
        (∀ u : F[X], algebraMap F[X] (RatFunc F) u ∈ A →
          ∃ c : Fin d → K[X], u = ∑ i, (c i).map (algebraMap K F) * a i) ∧
        (∀ c : Fin d → K[X], (∑ i, (c i).map (algebraMap K F) * a i).degree =
          Finset.univ.sup fun i => (a i).degree + (c i).degree) ∧
        ∀ k : ℕ, ∀ u : F[X],
          (algebraMap F[X] (RatFunc F) u ∈ A ∧ u.degree < k) ↔
            ∃ c : Fin d → K[X], (∀ i, (c i).degree + (a i).degree < k) ∧
              u = ∑ i, (c i).map (algebraMap K F) * a i := by sorry

end RSSubspaceDesign
