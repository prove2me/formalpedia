-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_normalInclusionCrossedModule
-- name    : QAlgorithms.Papers.Independent.Intake100.P20.normalInclusionCrossedModule
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:33:22.391051+00:00
-- url     : https://prove2.me/theorems/a8825a12-575f-403e-817c-9f28c85fa04c
-- title:
--   Normal inclusion is a crossed module for conjugation (source correction)
-- statement:
--   Let $N$ be a normal subgroup of a group $G$, and let $\partial:N\hookrightarrow G$ be inclusion. With conjugation $g\triangleright n=gng^{-1}$, inclusion is a crossed module:
--
--   $$\partial(g\triangleright n)=g\partial(n)g^{-1},\qquad \partial(n)\triangleright m=nmn^{-1}.$$
--
--   This standard example uses the two axioms printed immediately above it. The source prints “trivial action”; that word is corrected to “conjugation action” because equivariance for the injective inclusion forces conjugation. The literal printed claim fails for $N=G=S_3$. The source correction is disclosed in the theorem docstring and SOURCE_CORRECTIONS.md and requires independent moderation.
-- source:
--   Group Objects and Internal Categories, arXiv:math/0212065v1, PDF p. 9, §3, crossed-module example

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

namespace QAlgorithms.Papers.Independent.Intake100.P20

open CategoryTheory

open scoped TensorProduct Manifold ContDiff

universe u v w z

/-- PDF p. 9, corrected example: a normal subgroup inclusion is a crossed
module for CONJUGATION. Printed: "trivial action". Changed: "conjugation
 action". Equivariance of an injective inclusion forces conjugation; the
 printed claim fails for N = G = S3. See SOURCE_CORRECTIONS.md. Independent
 moderation of this source correction is still required. -/
theorem normalInclusionCrossedModule {G : Type u} [Group G]
    (N : Subgroup G) [N.Normal] :
    CrossedModule N.subtype (MulAut.conjNormal : G →* MulAut N) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P20
