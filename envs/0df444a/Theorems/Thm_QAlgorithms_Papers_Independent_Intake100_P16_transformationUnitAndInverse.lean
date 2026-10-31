-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P16_transformationUnitAndInverse
-- name    : QAlgorithms.Papers.Independent.Intake100.P16.transformationUnitAndInverse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:19:20.245373+00:00
-- url     : https://prove2.me/theorems/77bdbb6c-5791-422e-8e83-be9e8ee28969
-- title:
--   Lemma A.7: unit compatibility and inverse-pair naturality
-- statement:
--   Let $S,T$ be bicategories and $F_1,F_2:S\to T$ pseudofunctors, with unitors $u^1,u^2$. Let $\rho$ consist of object components $\rho_X:F_1(X)\to F_2(X)$ and invertible naturality cells $\rho_f:\rho_Y\circ F_1(f)\Rightarrow F_2(f)\circ\rho_X$, satisfying only the composition and 2-cell naturality axioms (T1) and (T2).
--
--   For every object $X$, unit compatibility follows:
--   $$
--   (u^2_X\circ\mathrm{id}_{\rho_X})\mathbin{\bullet}\rho_{\mathrm{id}_X}
--   =r_{\rho_X}^{-1}\mathbin{\bullet}l_{\rho_X}\mathbin{\bullet}(\mathrm{id}_{\rho_X}\circ u^1_X).
--   $$
--   Here $\bullet$ is vertical composition, $\circ$ is horizontal composition, and $l,r$ are the source's left and right unitors.
--
--   If additionally $S,T$ are strict and both $F_1,F_2$ are normalized, then
--   $$
--   \rho_{\mathrm{id}_X}=\mathrm{id}_{\rho_X\circ F_1(\mathrm{id}_X)}
--   =\mathrm{id}_{F_2(\mathrm{id}_X)\circ\rho_X},
--   \qquad
--   \rho_g\circ\mathrm{id}_{F_1(f)}=\mathrm{id}_{F_2(g)}\circ\rho_f^{-1}
--   $$
--   for every object $X$ and every $f:X\to Y$, $g:Y\to X$ with $g\circ f=\mathrm{id}_X$. Normalization means preservation of identities and all such inverse pairs, with identity unitors and the corresponding identity compositors.
--
--   This result supplies the unit axiom omitted from Definition A.6, including the additional inverse-pair identity used in normalized transport.
--
--   **Formalization Note** The input record omits Mathlib's unit axiom. Mathlib uses diagrammatic composition; its pseudofunctor compositor is inverse to the paper's. Heterogeneous equality records identity cells across the explicitly equal endpoints.
-- source:
--   Local Theory for 2-Functors on Path 2-Groupoids, arXiv:1303.4663v1, PDF p. 45, A.7

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P16

namespace QAlgorithms.Papers.Independent.Intake100.P16

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.MonoidalCategory

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe uS vS wS uT vT wT uC vC

/-- Lemma A.7, PDF pp.44–45. Part (i) derives the unit diagram from
T1 and T2. Only part (ii) requires strict bicategories and normalized
pseudofunctors. Both identity equalities and the inverse-pair equality
are retained; the inverse is on the naturality cell at f.
Normalization correction in (A.3), PDF p.43: printed c_f,g = id_idX;
changed to id_idF(X), because this compositor is a target 2-cell over F(X).
Only the identity subscript is corrected; the inverse-pair condition and
both conclusions of this lemma are unchanged. -/
theorem transformationUnitAndInverse
    {S : Type uS} [Bicategory.{wS, vS} S]
    {T : Type uT} [Bicategory.{wT, vT} T]
    (F G : Pseudofunctor S T) (r : UnitFreeStrongTrans F G) :
    (∀ X : S,
      (r.naturality (𝟙 X)).hom ≫ r.app X ◁ (G.mapId X).hom =
        (F.mapId X).hom ▷ r.app X ≫ (Bicategory.leftUnitor (r.app X)).hom ≫
          (Bicategory.rightUnitor (r.app X)).inv) ∧
    (Bicategory.Strict S → Bicategory.Strict T →
      IsNormalized F → IsNormalized G →
      (∀ X : S,
        HEq (r.naturality (𝟙 X)).hom (𝟙 (F.map (𝟙 X) ≫ r.app X)) ∧
        HEq (r.naturality (𝟙 X)).hom (𝟙 (r.app X ≫ G.map (𝟙 X)))) ∧
      (∀ {X Y : S} (f : X ⟶ Y) (g : Y ⟶ X), f ≫ g = 𝟙 X →
        HEq (F.map f ◁ (r.naturality g).hom)
          ((r.naturality f).inv ▷ G.map g))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P16
