-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P06_ordinary_hecke_inclusion
-- name    : QAlgorithms.Papers.Independent.Intake100.P06.ordinary_hecke_inclusion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:46:54.317077+00:00
-- url     : https://prove2.me/theorems/19b296f9-f6c0-4325-ab85-46003d7845da
-- title:
--   Canonical ordinary Hecke inclusion
-- statement:
--   Let $S$ be any commutative unital ring, let $q\in S^\times$, and let $n\ge1$. Write $H_{n,S}(q^2)$ for the ordinary braid-group algebra quotient and $\widehat H_{n,S}(q^2)$ for the type-$B_n$ Artin-group algebra quotient, in each case imposing $g_i-g_i^{-1}=q-q^{-1}$ on the ordinary braid generators. The affine generator $x_1$ satisfies the type-B braid relations and no quadratic relation. The generator-preserving $S$-algebra homomorphism
--   $$\iota:H_{n,S}(q^2)\longrightarrow\widehat H_{n,S}(q^2),\qquad g_i^{\pm1}\longmapsto g_i^{\pm1},$$
--   exists and is injective.
--
--   This supplies the canonical inclusion needed for left multiplication by the ordinary Hecke algebra. No genericity or domain assumption is required.
-- source:
--   Cyclotomic Birman--Wenzl--Murakami algebras, I: Freeness and realization as tangle algebras, arXiv:math/0612064v5, PDF p. 42, Section 6: inclusion of ordinary Hecke into affine Hecke

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P06

noncomputable section

open scoped BigOperators Classical TensorProduct

namespace QAlgorithms.Papers.Independent.Intake100.P06

open QAlgorithms.Papers.Independent.Support21.P14

/-- Section 6, PDF p.42: the canonical ordinary-to-affine map is injective.
No q-genericity, nonzero-ring, admissibility or BMW parameter assumptions. -/
theorem ordinary_hecke_inclusion (S : Type*) [CommRing S] (q : Sˣ)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ f : NormalizedBraidHecke S q n false →ₐ[S] NormalizedBraidHecke S q n true,
      Function.Injective f ∧
      ∀ i : ℕ, i + 1 < n → ∀ inverse : Bool,
        f (heckeG S q n false i inverse) = heckeG S q n true i inverse := by sorry

end QAlgorithms.Papers.Independent.Intake100.P06

end
