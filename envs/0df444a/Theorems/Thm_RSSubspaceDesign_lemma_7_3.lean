-- Prove2me | Theorems.Thm_RSSubspaceDesign_lemma_7_3
-- name    : RSSubspaceDesign.lemma_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:28:11.519203+00:00
-- url     : https://prove2.me/theorems/f4123f58-dbb8-4f0f-8008-8dac1ee3242f
-- title:
--   Lemma 7.3 — an element $\delta$ of prime degree $q$ whose sparse powers are independent, computable in $|K|^{O(q)}$ time
-- statement:
--   Let $K$ be a finite field, let $n,r\in\mathbb N$ satisfy $|K|>nr>2^r$, and let $q\ge2\cdot4^r$ be a prime. Then there is an element $\delta$ with $[K(\delta):K]=q$ such that for every $1\le h\le 2^r$ and all exponents $0\le e_1<\dots<e_h<nr$, the powers
--   $$\delta^{e_1},\dots,\delta^{e_h}$$
--   are linearly independent over $K$. Such a $\delta$ can be computed in time $|K|^{O(q)}$.
--
--   In the proof of Theorem 7.2, such a $\delta$ makes a Moore-type determinant nonzero, which yields condition (4.1) for the constructed points.
--
--   **Formalization Note** One Turing machine $M$ and one absolute constant $c$: on input $(p,f,n,r,q)$ it outputs the minimal polynomial $h_\delta$ of $\delta$ over $K$ (monic, irreducible, degree $q$) within $|K|^{cq}$ steps, and $\delta$ is the root of $h_\delta$ in $K[X]/(h_\delta)$.
--
--   Differences from the source:
--   - encoding: every finite field K → K = 𝔽_p[Y]/(f) for a prime p and a monic irreducible f ∈ 𝔽_p[Y], input as (p, f); reason: every finite field is isomorphic to one of these and the statement is invariant under isomorphism
--   - encoding: an element δ with [K(δ) : K] = q → the root of a monic irreducible h_δ ∈ K[X] of degree q in AdjoinRoot h_δ, output as the coefficient lists of h_δ; reason: K(δ) ≅ K[X]/(minpoly δ) with δ ↦ root; linear independence of powers is preserved
--   - reading: Such a δ can in fact be computed in |K|^{O(q)} time → one multi-stack Turing machine and one absolute c, chosen before K, n, r, q, halting within |K|^{c·q} steps on input (p, f, n, r, q); reason: O(q) without subscript is an absolute constant times q; the brute force of p.41 is uniform in all parameters
--   - encoding: 0 ≤ e₁ < ⋯ < e_h < nr → a strictly increasing e : Fin h → ℕ with e j < n * r; reason: Lean convention; same exponent sets
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Lemma 7.3, p.41 (PDF p.43)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RSSubspaceDesign_decPoly
import Definitions.Def_RSSubspaceDesign_IsCoeffList
import Definitions.Def_RSSubspaceDesign_encField

open Polynomial RSListDecodingCapacity.AllRates

namespace RSSubspaceDesign

/-- **Lemma 7.3.** Alrabiah–Goyal–Guruswami, arXiv:2610.36215 (held version, sha256
cf26424b…f36206), Lemma 7.3, p.41.

Let `K` be a finite field and let `n, r ∈ ℕ` satisfy `|K| > nr > 2^r`, and let `qᵢ ≥ 2·4^r` be a
prime. Then there exists a `δᵢ` with `[K(δᵢ) : K] = qᵢ` such that for any `1 ≤ h ≤ 2^r` and
`0 ≤ e₁ < ⋯ < e_h < nr`, the powers `δᵢ^{e₁}, …, δᵢ^{e_h}` are linearly independent over `K`. Such a
`δᵢ` can be computed in `|K|^{O(qᵢ)}` time.

**Formalization Note.** Existence and computation are stated together. `K` is input as a prime `p`
and a monic irreducible `f ∈ 𝔽_p[Y]` (`K = AdjoinRoot f`, `|K| = p^{deg f}`); every finite field is
isomorphic to one of these. `δ` is output as its minimal polynomial `h_δ ∈ K[X]` (monic,
irreducible, degree `q`), written as `q + 1` coefficient lists (`IsCoeffList`, `decPoly`), and `δ`
is the root of `h_δ` in `K(δ) = AdjoinRoot h_δ`, so `[K(δ) : K] = q`. One multi-stack Turing
machine `M` reads `K, n, r, q` (binary) and halts with this output within `|K|^{c·q}` steps, for one
absolute constant `c` (the `O(qᵢ)`). The exponents `e_j` are a strictly increasing
`e : Fin h → ℕ`; `nr` is the product `n·r`. -/
theorem lemma_7_3 :
    ∃ (c : ℕ) (M : Turing.TM2ComputableAux Bool Bool),
      ∀ (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X]) [Fact (Irreducible f)], f.Monic →
      ∀ n r q : ℕ, n * r < p ^ f.natDegree → 2 ^ r < n * r → q.Prime → 2 * 4 ^ r ≤ q →
        ∃ hc : List (List ℕ),
          IsCoeffList p f (q + 1) hc ∧
          HMBinPacking.OutputsWithin M (encField p f ++ encNat n ++ encNat r ++ encNat q)
            (encList (encList encNat) hc) ((p ^ f.natDegree) ^ (c * q)) ∧
          (decPoly p f hc).Monic ∧ Irreducible (decPoly p f hc) ∧
          (decPoly p f hc).natDegree = q ∧
          ∀ h : ℕ, 1 ≤ h → h ≤ 2 ^ r → ∀ e : Fin h → ℕ, StrictMono e → (∀ j, e j < n * r) →
            LinearIndependent (AdjoinRoot f)
              fun j => AdjoinRoot.root (decPoly p f hc) ^ e j := by sorry

end RSSubspaceDesign
