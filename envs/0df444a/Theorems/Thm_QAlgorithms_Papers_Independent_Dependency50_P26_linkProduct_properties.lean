-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_linkProduct_properties
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.linkProduct_properties
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:30:00.39397+00:00
-- url     : https://prove2.me/theorems/279e0158-fbc8-4bd8-b28d-9f8586c0ec26
-- title:
--   Theorem 2 (Properties of the link product)
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. For operators on overlapping sets of finite-dimensional wires, group their common factors together. The link product has swap symmetry, is associative when no wire occurs in all three operands, and preserves Hermiticity and positive semidefiniteness:
--
--   $$
--   M*N=E(N*M)E,\qquad M_1*(M_2*M_3)=(M_1*M_2)*M_3;\qquad M,N\succeq0\Longrightarrow M*N\succeq0.
--   $$
--
--   The associativity clause groups the six disjoint regions of the three wire-label sets. A missing region has dimension one. The separate Hermiticity clause is included in Lean. These are algebraic properties, without an additional causal-network assumption.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 3, Theorem 2 (Properties of the link product)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF pp.3–4, Theorem 2, all four clauses. Swap conjugation is expressed by the
basis swap; associativity groups the six disjoint Venn regions and therefore encodes
exactly the empty triple-intersection hypothesis. No network admissibility assumption
is imposed on these algebraic operators. -/
theorem linkProduct_properties :
    (∀ (X Y J : Type) [Fintype X] [Fintype Y] [Fintype J]
        [Nonempty X] [Nonempty Y] [Nonempty J]
        (M : Matrix (X × J) (X × J) ℂ) (N : Matrix (Y × J) (Y × J) ℂ),
      partialLink M N = regroup Prod.swap (partialLink N M) ∧
      (M.IsHermitian → N.IsHermitian → (partialLink M N).IsHermitian) ∧
      (M.PosSemidef → N.PosSemidef → (partialLink M N).PosSemidef)) ∧
    (∀ (A B C AB AC BC : Type)
        [Fintype A] [Fintype B] [Fintype C] [Fintype AB] [Fintype AC] [Fintype BC]
        [Nonempty A] [Nonempty B] [Nonempty C]
        [Nonempty AB] [Nonempty AC] [Nonempty BC]
        (M1 : Matrix (A × (AB × AC)) (A × (AB × AC)) ℂ)
        (M2 : Matrix (B × (AB × BC)) (B × (AB × BC)) ℂ)
        (M3 : Matrix (C × (AC × BC)) (C × (AC × BC)) ℂ),
      linkRightNested M1 M2 M3 = linkLeftNested M1 M2 M3) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
