-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P22_connected_generatedGroup_boundedProducts
-- name    : QAlgorithms.Papers.Independent.Renew46.P22.connected_generatedGroup_boundedProducts
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:29:59.307982+00:00
-- url     : https://prove2.me/theorems/ee433205-1af9-475f-b835-4ecc159f1722
-- title:
--   Chevalley: connected algebraic subgroups generate by uniformly bounded products
-- statement:
--   Let F have characteristic zero and let K be its specified algebraic closure. For a finite nonempty family G₁,…,Gₛ of connected algebraic subgroups of GLₙ(K), let H be their ordinary generated subgroup. Then H is algebraic and connected, and there is one integer m>0 such that every h in H is a product of exactly m elements, each in some Gᵢ. The bound m is chosen before h; identity factors allow padding.
-- source:
--   Constructing algebraic groups from their Lie algebras, arXiv:math/0612557v1, PDF p. 3, Theorem 1 (Chevalley)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P22

open scoped BigOperators Pointwise

attribute [local instance 100] LieRing.ofAssociativeRing

section Geometric

variable {F K : Type*} [Field F] [hchar : CharZero F] [Field K] [Algebra F K] [hclosure : IsAlgClosure F K]

variable {n : ℕ}

section

include hchar hclosure

/-- Theorem 1 (Chevalley), PDF p.3, cited there from [2], Chapter II, section 7,
Corollary 3. A single positive word length works for every element of the ordinary
generated subgroup. The finite displayed family is nonempty. -/
theorem connected_generatedGroup_boundedProducts {s : ℕ} (hs : 0 < s)
    (G : Fin s → Subgroup (GeometricGL n K))
    (hG : ∀ i, IsAlgebraicGroup (G i))
    (hc : ∀ i, IsZariskiConnected (G i : Set (GeometricGL n K))) :
    IsAlgebraicGroup (⨆ i, G i) ∧
    IsZariskiConnected ((⨆ i, G i : Subgroup (GeometricGL n K)) : Set (GeometricGL n K)) ∧
    ∃ m : ℕ, 0 < m ∧ ∀ h ∈ (⨆ i, G i : Subgroup (GeometricGL n K)),
      ∃ factors : List (GeometricGL n K), factors.length = m ∧
        (∀ a ∈ factors, ∃ i : Fin s, a ∈ G i) ∧ factors.prod = h := by sorry

end

end Geometric

end QAlgorithms.Papers.Independent.Renew46.P22

end
