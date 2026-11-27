-- Prove2me | Theorems.Thm_PrivPCP_places_rational
-- name    : PrivPCP.places_rational
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:12:32.368989+00:00
-- url     : https://prove2.me/theorems/edfe57d7-2441-5692-b604-64cb681a5186
-- title:
--   Places of a rational function field $K(z)$: $\operatorname{ord}_v p(z)=\operatorname{mult}_{c_v}(p)$
-- statement:
--   This is the classification of the finite places of a rational function field over an algebraically closed field.
--
--   Let $K$ be algebraically closed, and let $L=K(z)$ be generated over $K$ by a transcendental element $z$. To each place $v$ of $L/K$ at which $z$ is integral ($\operatorname{ord}_v z\ge0$) there is attached a point $c_v\in K$, the residue of $z$ at $v$, with the following properties:
--
--   1. **Order of a polynomial.** For every nonzero polynomial $p\in K[T]$,
--   $$\operatorname{ord}_v\big(p(z)\big)=\operatorname{mult}_{c_v}(p),$$
--      the multiplicity of $c_v$ as a root of $p$.
--   2. **Injectivity.** Distinct such places have distinct points $c_v$.
--
--   Equivalently, the valuation ring of $v$ is the localization $K[z]_{(z-c_v)}$. The finite places of $K(z)$ are therefore exactly the points of the affine line (Stichtenoth, Theorem 1.2.2). In the proof of Lemma 4.13 this reduces the count $\Gamma_F$ on a rational (binomial) curve to counting common roots of two polynomials.
--
--   **Formalization Note** Places are `AlgebraicCurve.Place K L`, the discrete valuation subrings of $L$ containing $K$, with normalized order `ord`. The map $v\mapsto c_v$ is given on all places, but it is only meaningful, and only asserted to be injective, on those with $\operatorname{ord}_v z\ge0$.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., Springer GTM 254 (2009), Theorem 1.2.2 (places of the rational function field K(x)); used in the dependent case of Lemma 4.13 of Bafna, Vyas, Private PCPs from Product Expansion (STOC 2027 submission, sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), p.25

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

namespace PrivPCP

theorem places_rational : ∀ (K L : Type) [Field K] [IsAlgClosed K] [Field L] [Algebra K L] (z : L),
    Transcendental K z → IntermediateField.adjoin K {z} = ⊤ →
    ∃ res : AlgebraicCurve.Place K L → K,
      (∀ v w : AlgebraicCurve.Place K L, 0 ≤ v.ord z → 0 ≤ w.ord z → res v = res w → v = w) ∧
      ∀ v : AlgebraicCurve.Place K L, 0 ≤ v.ord z → ∀ p : Polynomial K, p ≠ 0 →
        v.ord (Polynomial.aeval z p) = (p.rootMultiplicity (res v) : ℤ) := by
  sorry

end PrivPCP
