-- Prove2me | Theorems.Thm_ReplParity_poly_hash_uniform
-- name    : ReplParity.poly_hash_uniform
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T11:42:13.608974+00:00
-- url     : https://prove2.me/theorems/72bc6fbf-6b8e-4755-a956-fd93dd059823
-- title:
--   Proof of Lemma 3.2, p.16 — a random polynomial of degree $<2\kappa$ is uniform on $2\kappa$ points [WC81]
-- statement:
--   Let $F$ be a finite field, $\kappa\ge0$, and $x_0,\dots,x_{2\kappa-1}\in F$ distinct. The map sending a coefficient vector $c\in F^{2\kappa}$ to the value vector
--   $$\Big(\sum_{\ell<2\kappa}c_\ell\,x_i^{\ell}\Big)_{i<2\kappa}$$
--   is a bijection of $F^{2\kappa}$; equivalently, every value vector has exactly one coefficient vector. Hence a polynomial of degree less than $2\kappa$ with independent uniform coefficients takes independent uniform values on the points $x_i$.
--
--   Differences from the source:
--   - generalization: the field 𝔽_{2^b} → any finite field; reason: specializes to 𝔽_{2^b}
--   - encoding: independent uniform values → the coefficient-to-value map is a bijection, each value vector having exactly one preimage; reason: a bijection pushes the uniform law on coefficients to the uniform law on values
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), proof of Lemma 3.2, p.16 (PDF p.18), citing [WC81]

import Mathlib
import Definitions.Def_ReplParity_tokenMinHash

namespace ReplParity

/-- **A random polynomial of degree less than 2κ is uniform on 2κ distinct points [WC81].** Shen,
Zhong, *Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC
2027 submission (manuscript sha256 40424491…), proof of Lemma 3.2, p.16 (PDF p.18): "A polynomial
of degree less than 2κ with independent uniform coefficients takes independent uniform values on any
2κ distinct points [WC81], because the Vandermonde matrix of these points is invertible."

For a finite field `F` and distinct points `x_0, …, x_{2κ−1}`, the map from coefficient vectors
`c ∈ F^{2κ}` to value vectors `(h_c(x_i))_i`, `h_c(x) = Σ_{ℓ<2κ} c_ℓ x^ℓ`, is a bijection; so every
value vector has exactly one preimage, and uniform coefficients give independent uniform values. -/
theorem poly_hash_uniform {F : Type*} [Field F] [Fintype F] [DecidableEq F] (κ : ℕ)
    (x : Fin (2 * κ) → F) (hx : Function.Injective x) :
    Function.Bijective (fun c : Fin (2 * κ) → F => fun i => polyHash c (x i)) ∧
    ∀ t : Fin (2 * κ) → F,
      (Finset.univ.filter (fun c : Fin (2 * κ) → F => (fun i => polyHash c (x i)) = t)).card = 1 := by sorry

end ReplParity
