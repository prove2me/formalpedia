-- Prove2me | Theorems.Thm_Rep_isZero_tateCohomology_of_retract
-- name    : Rep.isZero_tateCohomology_of_retract
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/377a52b8-1cfb-5e27-b807-3f911478bf0b
-- title:
--   Vanishing of Tate cohomology passes to retracts
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, and let $A$, $B$ be objects of $\mathrm{Rep}\,k\,G$, i.e. $k$-linear representations of $G$. Suppose given morphisms of representations $i : A \to B$ and $r : B \to A$ whose composite $i$ followed by $r$ is the identity of $A$, so that $A$ is a retract of $B$. Let $q$ be an integer and suppose that the object $B.\mathrm{tateCohomology}\ q$ of $\mathrm{ModuleCat}\,k$ is a zero object. The conclusion is that $A.\mathrm{tateCohomology}\ q$ is a zero object as well. Here `tateCohomology` is defined degreewise: in degree $n+1 \ge 1$ it is the group cohomology $H^{n+1}$ of the representation, in degree $0$ the quotient of the invariants by the range of the norm map $\rho.\mathrm{normBar}$, in degree $-1$ the kernel of that norm map, and in degree $-(n+2) \le -2$ the group homology $H_{n+1}$.
--
--   This is the standard observation that Tate cohomology, being functorial in the representation, sends retracts to retracts, so that acyclicity is inherited by direct summands. It is used to deduce Tate-acyclicity of summands of free and of induced (tensored) representations, in [`Rep.isZero_tateCohomology_res_free`](thm.html#Rep.isZero_tateCohomology_res_free) and [`Rep.isZero_tateCohomology_res_tensor_of_forall_isZero`](thm.html#Rep.isZero_tateCohomology_res_tensor_of_forall_isZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_isZero_tateCohomology_of_retract.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.isZero_tateCohomology_of_retract {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {A B : Rep.{u} k G} (i : A ⟶ B) (r : B ⟶ A) (hir : i ≫ r = 𝟙 A) (q : ℤ)
    (hB : CategoryTheory.Limits.IsZero (B.tateCohomology q)) :
    CategoryTheory.Limits.IsZero (A.tateCohomology q) := by sorry
