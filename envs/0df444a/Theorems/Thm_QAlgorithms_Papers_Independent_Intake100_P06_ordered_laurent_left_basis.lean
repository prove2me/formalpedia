-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P06_ordered_laurent_left_basis
-- name    : QAlgorithms.Papers.Independent.Intake100.P06.ordered_laurent_left_basis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:47:50.343821+00:00
-- url     : https://prove2.me/theorems/510cdac8-3054-4612-9e93-9014bc1d1473
-- title:
--   Ordered Laurent basis as a left Hecke module
-- statement:
--   Let $S$ be any commutative unital ring, let $q\in S^\times$, and let $n\ge1$. Regard the affine Hecke algebra $\widehat H_{n,S}(q^2)$ as a left module over the ordinary Hecke algebra $H_{n,S}(q^2)$ through the canonical generator-preserving inclusion. Put $x'_j=g_{j-1}\cdots g_1x_1g_1^{-1}\cdots g_{j-1}^{-1}$. Then
--   $$\bigl((x'_n)^{a_n}\cdots(x'_1)^{a_1}\bigr)_{a\in\mathbb Z^n}$$
--   is a basis of this left module.
--
--   The order of the factors is part of the assertion; no commutativity of the elements $x'_j$ is assumed. It separates ordinary Hecke coefficients on the left from the integer winding data.
-- source:
--   Cyclotomic Birman--Wenzl--Murakami algebras, I: Freeness and realization as tangle algebras, arXiv:math/0612064v5, PDF p. 42, Section 6: ordered Laurent basis over ordinary Hecke

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P06

noncomputable section

open scoped BigOperators Classical TensorProduct

namespace QAlgorithms.Papers.Independent.Intake100.P06

open QAlgorithms.Papers.Independent.Support21.P14

/-- Ordered Laurent basis announced on PDF pp.42--43 and obtained from
Proposition 6.8, p.44. The module is LEFT multiplication through the specified
inclusion. No commutativity of the winding conjugates is asserted. -/
theorem ordered_laurent_left_basis (S : Type*) [CommRing S] (q : Sˣ)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ f : NormalizedBraidHecke S q n false →ₐ[S] NormalizedBraidHecke S q n true,
      Function.Injective f ∧
      (∀ i : ℕ, i + 1 < n → ∀ inverse : Bool,
        f (heckeG S q n false i inverse) = heckeG S q n true i inverse) ∧
      (letI : Module (NormalizedBraidHecke S q n false) (NormalizedBraidHecke S q n true) :=
          Module.compHom (NormalizedBraidHecke S q n true) f.toRingHom
       ∃ b : Module.Basis (Fin n → ℤ) (NormalizedBraidHecke S q n false) (NormalizedBraidHecke S q n true),
         ∀ a, b a = heckeLaurentWord S q n a) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P06

end
