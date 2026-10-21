-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P27_factorSystem_group_and_formulas
-- name    : QAlgorithms.Papers.Independent.Renew46.P27.factorSystem_group_and_formulas
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:52:55.738247+00:00
-- url     : https://prove2.me/theorems/98ca7cb3-7f22-47b8-b319-dec209a4e7cc
-- title:
--   Normalized factor systems: group criterion, inversion and conjugation
-- statement:
--   Let $G$ and $N$ be groups. Let $S:G\to\operatorname{Aut}(N)$ and $\omega:G^2\to N$ satisfy $S(1)=\mathrm{id}$, $\omega(1,g)=\omega(g,1)=1$, and $S(g)S(h)=C_{\omega(g,h)}S(gh)$, where $C_a(n)=ana^{-1}$. Put
--   $$
--   (n,g)\star(m,h)=(nS(g)(m)\omega(g,h),gh),\qquad
--   (d_S\omega)(g,h,k)=S(g)(\omega(h,k))\omega(g,hk)\omega(gh,k)^{-1}\omega(g,h)^{-1}.
--   $$
--   Then $\star$ is a group multiplication on $N\times G$ if and only if $d_S\omega$ is identically $1$. In every group structure with this multiplication the identity is $(1,1)$ and
--   $$
--   (n,g)^{-1}=(S(g)^{-1}(n^{-1}\omega(g,g^{-1})^{-1}),g^{-1})
--   =(\omega(g^{-1},g)^{-1}S(g^{-1})(n^{-1}),g^{-1}).
--   $$
--   In particular,
--   $$
--   (1,g)^{-1}=(S(g)^{-1}(\omega(g,g^{-1})^{-1}),g^{-1})
--   =(\omega(g^{-1},g)^{-1},g^{-1}).
--   $$
--   Writing $\omega_g(x)=\omega(g,x)\omega(gxg^{-1},g)^{-1}$, conjugation is
--   $$
--   (n,g)\star(m,h)\star(n,g)^{-1}
--   =(nS(g)(m)\omega_g(h)S(ghg^{-1})(n^{-1}),ghg^{-1}).
--   $$
--   The two special cases are
--   $$
--   (n,1)\star(m,h)\star(n,1)^{-1}=(nmS(h)(n^{-1}),h),\qquad
--   (1,g)\star(m,h)\star(1,g)^{-1}=(S(g)(m)\omega_g(h),ghg^{-1}).
--   $$
--   This gives the algebraic group structure used before constructing the local Lie atlas; it makes no claim that the global product topology yields a Lie group.
--
--   **Formalization Note** Normalization is explicit because the source proof uses it. The general conjugation formula removes the erroneous inverse printed on $S(ghg^{-1})$, as dictated by the preceding compatibility calculation; independent moderation of this correction is pending.
-- source:
--   Non-abelian extensions of infinite-dimensional Lie groups, arXiv:math/0504295v1, PDF p. 15, Lemma II.7 (continues on PDF p. 16)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P27

namespace QAlgorithms.Papers.Independent.Renew46.P27

universe u v

variable {G : Type u} {N : Type v} [Group G] [Group N]

/-- Lemma II.7, arXiv:math/0504295v1, PDF pp. 15–16: group criterion,
both inversion formulas, their (1,g) specializations, and conjugation with
both special cases (2.7). This is the abstract-group lemma, not a statement
that the product manifold is a Lie group. The proof's implicit normalization
is made explicit. Source correction: the printed general conjugation formula
has S(gg' g^-1)^-1; compatibility reduces the preceding proof line to
S(gg' g^-1), so the erroneous inverse is removed. The real semidirect-product
counterexample and independent-review requirement are recorded in the unit.
Every operation using grp is explicitly projected from that group structure,
so the ambient componentwise product instance cannot enter these conclusions. -/
theorem factorSystem_group_and_formulas
    (S : G → MulAut N) (omega : G → G → N)
    (hS : S 1 = MulEquiv.refl N)
    (hNormalized : NormalizedTwoCochain omega)
    (hCompatible : CompatibleFactorData S omega) :
    (AdmitsExtensionGroup S omega ↔ IsFactorCocycle S omega) ∧
    (∀ grp : Group (N × G), grp.mul = extensionProduct S omega →
      grp.one = (1, 1) ∧
      (∀ n g,
        grp.inv (n, g) = ((S g).symm (n⁻¹ * (omega g g⁻¹)⁻¹), g⁻¹) ∧
        grp.inv (n, g) = ((omega g⁻¹ g)⁻¹ * S g⁻¹ n⁻¹, g⁻¹)) ∧
      (∀ g,
        grp.inv (1, g) = ((S g).symm ((omega g g⁻¹)⁻¹), g⁻¹) ∧
        grp.inv (1, g) = ((omega g⁻¹ g)⁻¹, g⁻¹)) ∧
      (∀ n g n2 g2,
        grp.mul (grp.mul (n, g) (n2, g2)) (grp.inv (n, g)) =
          (n * S g n2 * conjugationCochain omega g g2 *
            S (g * g2 * g⁻¹) n⁻¹, g * g2 * g⁻¹)) ∧
      (∀ n n2 g2,
        grp.mul (grp.mul (n, 1) (n2, g2)) (grp.inv (n, 1)) =
          (n * n2 * S g2 n⁻¹, g2)) ∧
      (∀ g n2 g2,
        grp.mul (grp.mul (1, g) (n2, g2)) (grp.inv (1, g)) =
          (S g n2 * conjugationCochain omega g g2, g * g2 * g⁻¹))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P27
