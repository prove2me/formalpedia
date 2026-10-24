-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P35_power_purity_family
-- name    : QAlgorithms.Papers.Independent.Support50.P35.power_purity_family
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:46:51.634108+00:00
-- url     : https://prove2.me/theorems/76abd2a3-7c09-4187-8861-bf2db070bb41
-- title:
--   Power-purity costs and their product-state zero set
-- statement:
--   Let \(1\leq N\leq M\), let \(a\in\mathbb N\) with \(a>1\), and put \(f_a(\rho)=2(1-\operatorname{tr}(\rho^a))\) for density matrices on \(\mathbb C^M\). The function is continuous, unitarily invariant, and concave: for every unitary \(U\), density matrices \(\omega_1,\omega_2\), and \(p\in[0,1]\),
--
--   $$
--   f_a(U\rho U^\dagger)=f_a(\rho),\qquad
--   f_a(p\omega_1+(1-p)\omega_2)\geq p f_a(\omega_1)+(1-p)f_a(\omega_2).
--   $$
--
--   It vanishes on normalized pure density matrices. For every unit vector \(\psi\in\mathbb C^M\otimes\mathbb C^N\),
--
--   $$
--   f_a(\operatorname{tr}_B|\psi\rangle\langle\psi|)=0
--   \iff \psi=u\otimes v\text{ for unit vectors }u,v.
--   $$
--
--   The partial trace removes the second factor, and the coefficient 2 is literal. This supplies the source's family of pure-state marginal costs and its exact product-state zero set.
-- source:
--   Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction, arXiv:quant-ph/0402055v2, PDF p. 18, Unnumbered Eq.(56): properties of power-purity costs and pure-state zero set

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

/-- PDF p.18, Eq.(56): unitary invariance, concavity, pure-state vanishing,
and exactly the product-vector zero set for the induced pure bipartite cost. -/
theorem power_purity_family (M N a : ℕ) (hN : 0 < N) (hNM : N ≤ M) (ha : 1 < a) :
    IsMarginalCost (powerPurityCost (I := Fin M) a) ∧
    (∀ rho : Matrix (Fin M) (Fin M) ℂ, QAlgorithms.Papers.Independent.Information100.P08.IsPure rho → powerPurityCost a rho = 0) ∧
    (∀ psi : EuclideanSpace ℂ (Fin M × Fin N), IsState psi →
      (powerPurityCost a (traceRight (pureDensity psi)) = 0 ↔
        ∃ u : EuclideanSpace ℂ (Fin M), ∃ v : EuclideanSpace ℂ (Fin N),
          IsState u ∧ IsState v ∧ psi = tensorVec u v)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P35

end
