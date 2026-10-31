-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_crossedKernelAndImage
-- name    : QAlgorithms.Papers.Independent.Intake100.P20.crossedKernelAndImage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:33:53.069285+00:00
-- url     : https://prove2.me/theorems/ff198670-4981-49cb-9b0e-6ae71e9ed70d
-- title:
--   A crossed module has abelian kernel and normal image
-- statement:
--   Let $C$ and $G$ be groups, let $\partial:C\to G$ be a homomorphism, and let $G$ act on $C$ by group automorphisms. Assume $\partial(g\triangleright c)=g\partial(c)g^{-1}$ and $\partial(c)\triangleright d=cdc^{-1}$. Then
--
--   $$\ker\partial\text{ is abelian},\qquad \operatorname{im}\partial\triangleleft G.$$
--
--   No injectivity, surjectivity or faithfulness assumption is imposed. This records both structural consequences asserted by the source.
-- source:
--   Group Objects and Internal Categories, arXiv:math/0212065v1, PDF p. 9, §3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

namespace QAlgorithms.Papers.Independent.Intake100.P20

open CategoryTheory

open scoped TensorProduct Manifold ContDiff

universe u v w z

/-- PDF p. 9: BOTH the abelian-kernel and normal-image consequences,
without injectivity, surjectivity, or faithful-action assumptions. -/
theorem crossedKernelAndImage {C : Type u} {G : Type v} [Group C] [Group G]
    (boundary : C →* G) (action : G →* MulAut C) (h : CrossedModule boundary action) :
    (∀ a b : boundary.ker, a * b = b * a) ∧ boundary.range.Normal := by sorry

end QAlgorithms.Papers.Independent.Intake100.P20
