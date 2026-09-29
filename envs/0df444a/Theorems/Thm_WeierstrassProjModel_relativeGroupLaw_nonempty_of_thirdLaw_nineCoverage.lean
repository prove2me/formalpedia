-- Prove2me | Theorems.Thm_WeierstrassProjModel_relativeGroupLaw_nonempty_of_thirdLaw_nineCoverage
-- name    : WeierstrassProjModel.relativeGroupLaw_nonempty_of_thirdLaw_nineCoverage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/40f7a53c-513d-5f89-af6d-a60db649f44d
-- title:
--   Relative group law on the projective model from a nine-element chart coverage
-- statement:
--   Let $R$ be a Noetherian commutative integral domain and $W$ a Weierstrass curve over $R$ that is elliptic, and write $\mathcal{A}_i$ for the degree-zero homogeneous localization of the graded ring $\mathrm{MvPolynomial}(\mathrm{Fin}\,3, R)/(W.\mathrm{polynomial})$ away from the class of $X_i$, so that $E =$ `projModelCR W.toProjective` is the $\mathrm{Proj}$ of this graded quotient. Suppose given, for each pair $(i,j) \in \mathrm{Fin}\,3 \times \mathrm{Fin}\,3$, three elements $u_3(i,j,k) \in \mathcal{A}_i \otimes_R \mathcal{A}_j$ together with morphisms $\tau_{ijk} \colon \operatorname{Spec}(\mathcal{A}_i \otimes_R \mathcal{A}_j)_{u_3(i,j,k)} \to E$, subject to two conditions: (i) for every $(i,j)$ the six Lange–Ruppert elements `kw_lrSixU W i j` (the chart elements $\mathrm{kw\_lrChart\_u}$ and their symmetric counterparts, indexed by $\mathrm{Fin}\,3 \oplus \mathrm{Fin}\,3$) together with the three elements $u_3(i,j,\cdot)$ span the unit ideal of $\mathcal{A}_i \otimes_R \mathcal{A}_j$; and (ii) for all $i,j,k$ and all $l \in \mathrm{Fin}\,3 \oplus \mathrm{Fin}\,3$, the morphisms $\tau_{ijk}$ and `kw_lrSixU_toE W i j l` agree after pulling back along the two localization maps, i.e. on the fibre product of $\operatorname{Spec}(\mathcal{A}_i \otimes_R \mathcal{A}_j)_{u_3(i,j,k)}$ and $\operatorname{Spec}(\mathcal{A}_i \otimes_R \mathcal{A}_j)_{\mathrm{kw\_lrSixU}\,W\,i\,j\,l}$ over $\operatorname{Spec}(\mathcal{A}_i \otimes_R \mathcal{A}_j)$. Then the type `RelativeGroupLaw R (projModelStrCR W.toProjective)` is nonempty: the structure morphism $\pi \colon E \to \operatorname{Spec} R$ (given by $\mathrm{Proj.toSpecZero}$ followed by $\operatorname{Spec}$ of the structure map $R \to (\text{degree-}0\text{ part})$) admits multiplication, unit and inversion operations on $T$-points over $\operatorname{Spec} R$, for every scheme $T$ with a morphism $t$ to $\operatorname{Spec} R$, satisfying associativity, both unit laws, left inversion, and naturality of the multiplication under morphisms $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$.
--
--   This is the glueing half of the construction of the group law on the projective Weierstrass model over a Noetherian domain: it converts a nine-element coverage of each of the nine affine charts of $E \times_R E$, by the six Lange–Ruppert addition-law charts and a third family, together with pairwise agreement of the associated addition morphisms, into a functorial group structure on the $T$-points of $E$ over $\operatorname{Spec} R$. It is used by `relativeGroupLaw_nonempty_of_isElliptic_of_baseChangeIso_of_isNoetherianRing`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_relativeGroupLaw_nonempty_of_thirdLaw_nineCoverage.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

theorem WeierstrassProjModel.relativeGroupLaw_nonempty_of_thirdLaw_nineCoverage
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (u₃ : ∀ (i j : Fin 3), Fin 3 → (𝒜 i) ⊗[R] (𝒜 j))
    (toE₃ : ∀ (i j k : Fin 3),
      Spec (CommRingCat.of (Localization.Away (u₃ i j k))) ⟶ projModelCR W.toProjective)
    (hcov₉ : ∀ i j, Ideal.span (Set.range (kw_lrSixU W i j) ∪ Set.range (u₃ i j))
      = (⊤ : Ideal ((𝒜 i) ⊗[R] (𝒜 j))))
    (hcompat₃ : ∀ (i j k : Fin 3) (l : Fin 3 ⊕ Fin 3),
      pullback.fst
          (Spec.map (CommRingCat.ofHom
            (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ i j k)))))
          (kw_lrSixU_locMap W i j l)
        ≫ toE₃ i j k
      = pullback.snd
          (Spec.map (CommRingCat.ofHom
            (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ i j k)))))
          (kw_lrSixU_locMap W i j l)
        ≫ kw_lrSixU_toE W i j l) :
    Nonempty (WeierstrassProjModel.RelativeGroupLaw R (projModelStrCR W.toProjective)) := by sorry
