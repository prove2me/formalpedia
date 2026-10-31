-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_crossedModulesAndInternalCategories
-- name    : QAlgorithms.Papers.Independent.Intake100.P20.crossedModulesAndInternalCategories
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:34:17.14413+00:00
-- url     : https://prove2.me/theorems/2929b219-3cac-4c1e-a6fa-b05e7744aa1c
-- title:
--   Crossed modules and internal Grp categories: both constructions
-- statement:
--   Let $\partial:C\to G$, with an automorphic left action $\rho:G\to\operatorname{Aut}(C)$, be a crossed module. It determines an internal Grp category with objects $G$, arrows $C\rtimes_\rho G$, and
--
--   $$s(c,g)=g,\quad t(c,g)=\partial(c)g,\quad e(g)=(1,g),\quad (d,\partial(c)g)\circ(c,g)=(dc,g).$$
--
--   Conversely, for an internal Grp category $(A,O,s,t,e,\circ)$, the actual subgroup $K=\ker s$, boundary $\partial=t|_K$, and action $x\triangleright k=e(x)ke(x)^{-1}$ form a crossed module. The canonical group isomorphism $a\mapsto(ae(s(a))^{-1},s(a))$ identifies the original category with the category reconstructed from this crossed module: it preserves source, target, identities and every defined composite. In particular the semidirect composition formula is a conclusion of the internal-category axioms.
--
--   Starting instead from $(C,G,\partial,\rho)$, the map $c\mapsto(c,1)$ identifies $C$ with the reconstructed source kernel and preserves boundary and action. Thus both constructions recover their original structures through the explicit canonical identifications. This is the source's structural correspondence, without an additional assertion about categories of morphisms.
-- source:
--   Group Objects and Internal Categories, arXiv:math/0212065v1, PDF p. 9, §3, Crossed Modules and Internal Categories, pp. 9–12

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

namespace QAlgorithms.Papers.Independent.Intake100.P20

open CategoryTheory

open scoped TensorProduct Manifold ContDiff

universe u v w z

/-- PDF pp. 9–12: BOTH explicit constructions and reconstruction compatibility.
The forward category has s(c,g)=g, t(c,g)=boundary(c)g, identity(g)=(1,g),
and (d,boundary(c)g) after (c,g) = (dc,g). The reverse crossed module is
the source kernel with restricted target and identity-conjugation action.
The original category is recovered by its computed semidirect coordinates,
including composition as a CONCLUSION of the category/interchange laws.
The original crossed module is recovered by c ↦ (c,1) in the source kernel.
No claim about a category of crossed-module morphisms is silently added. -/
theorem crossedModulesAndInternalCategories :
    (∀ {C : Type u} {G : Type v} [Group C] [Group G]
      (d : C →* G) (r : G →* MulAut C), CrossedModule d r →
      InternalCategoryInGrp (crossedCategoryMaps d r) ∧
      ∃ q : C ≃* (SemidirectProduct.rightHom : SemidirectProduct C G r →* G).ker,
        (∀ c, q c = crossedKernelMap r c) ∧
        (∀ c, (crossedCategoryMaps d r).target (q c).val = d c) ∧
        (∀ g c, (q (r g c)).val =
          (crossedCategoryMaps d r).identity g * (q c).val *
            ((crossedCategoryMaps d r).identity g)⁻¹)) ∧
    (∀ {A : Type u} {O : Type v} [Group A] [Group O]
      (D : CategoryMaps A O) (h : InternalCategoryInGrp D),
      CrossedModule (kernelBoundary D h) (kernelAction D h) ∧
      InternalCategoryInGrp (crossedCategoryMaps (kernelBoundary D h) (kernelAction D h)) ∧
      ∃ q : A ≃* SemidirectProduct (sourceHom D h).ker O (kernelAction D h),
        (∀ a, q a = categoryCoordinates D h a) ∧
        (∀ a, (q a).right = D.source a ∧
          kernelBoundary D h (q a).left * (q a).right = D.target a) ∧
        (∀ x, q (D.identity x) = ⟨1, x⟩) ∧
        (∀ f g, D.target f = D.source g →
          q (D.compose g f) = ⟨(q g).left * (q f).left, (q f).right⟩)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P20
