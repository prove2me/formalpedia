-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_groupObjectsInGrp
-- name    : QAlgorithms.Papers.Independent.Intake100.P20.groupObjectsInGrp
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:27:18.287064+00:00
-- url     : https://prove2.me/theorems/90bc7eee-b900-4fbb-9100-09fcb2f98c4d
-- title:
--   Group objects in Grp are exactly abelian groups
-- statement:
--   Let $G$ be a group with its given multiplication $\cdot$. A group object on $G$ consists of another multiplication $m$, an identity point $e$, and an inverse map $i$, satisfying associativity, both unit laws, and both inverse laws, with all three maps homomorphisms for the given group structures (and the componentwise product on $G\times G$). Every such object satisfies
--
--   $$m(x,y)=x\cdot y,\qquad e=1_G,\qquad i(x)=x^{-1},\qquad x\cdot y=y\cdot x.$$
--
--   Conversely, if $G$ is abelian, its given multiplication, identity and inversion define a group object in Grp. This identifies the possible internal group structures and their underlying groups.
-- source:
--   Group Objects and Internal Categories, arXiv:math/0212065v1, PDF p. 1, §1, pp. 3–4; abstract

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

namespace QAlgorithms.Papers.Independent.Intake100.P20

open CategoryTheory

open scoped TensorProduct Manifold ContDiff

universe u v w z

/-- PDF pp. 3–4, also abstract p. 1: group objects in Grp are exactly
abelian groups. Every internal multiplication equals the original multiplication;
conversely the canonical maps of every abelian group give a group object. -/
theorem groupObjectsInGrp {G : Type u} [Group G] :
    (∀ D : GroupMaps G, GroupObjectInGrp D →
      (∀ a b : G, a * b = b * a) ∧
      (∀ a b, D.mul a b = a * b) ∧ D.unit = 1 ∧
      (∀ a, D.inverse a = a⁻¹)) ∧
    ((∀ a b : G, a * b = b * a) → GroupObjectInGrp (mapsOfGroup G)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P20
