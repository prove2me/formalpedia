-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_symplectic_fundamental_group
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.symplectic_fundamental_group
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:16:23.445632+00:00
-- url     : https://prove2.me/theorems/f8472932-8544-47e7-80a5-892137ca12ad
-- title:
--   Corollary 9
-- statement:
--   For $n\ge1$, let $\mathcal S$ be the vector space of real symmetric matrices in $\mathfrak{sp}(2n,\mathbb R)$. Then
--
--   $$\operatorname{Sp}(2n,\mathbb R)\cong_{\rm top} S^1\times SU(n)\times\mathcal S,\qquad \pi_1(\operatorname{Sp}(2n,\mathbb R),I)\cong\mathbb Z.$$
--
--   Every continuous map from the symplectic group to the circle that agrees with the complex determinant on $U(n)$ sends $I$ to $1$ and induces an isomorphism on fundamental groups. The printed adjective “symplectic” for the vector-space factor is corrected to “symmetric”, as determined by Theorem 7. This identifies the homotopy invariant measured by rotation winding.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 8, Corollary 9

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Corollary 9, PDF p.8. Printed 'symplectic matrices in the Lie algebra' is
corrected to 'symmetric matrices', as determined by Theorem 7. -/
theorem symplectic_fundamental_group {n : ℕ} (hn : 1 ≤ n) :
    Nonempty (SymplecticSpace n ≃ₜ (UnitCircle × SpecialUnitary n × SymmetricLieSpace n)) ∧
    (∀ e : SymplecticSpace n, e.val = 1 →
      Nonempty (FundamentalGroup (SymplecticSpace n) e ≃* Multiplicative ℤ)) ∧
    (∀ f : C(SymplecticSpace n, UnitCircle),
      (∀ A : SymplecticSpace n, IsUnitaryReal A.val → (f A).val = complexActionDet A.val) →
      ∀ e : SymplecticSpace n, e.val = 1 →
        (f e).val = 1 ∧ Function.Bijective (FundamentalGroup.map f e)) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
