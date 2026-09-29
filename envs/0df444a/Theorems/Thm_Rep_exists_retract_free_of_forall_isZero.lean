-- Prove2me | Theorems.Thm_Rep_exists_retract_free_of_forall_isZero
-- name    : Rep.exists_retract_free_of_forall_isZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/40c1c57d-48e2-519d-9b3f-5b96da6c9b21
-- title:
--   Cohomologically trivial ℤ-free representations are retracts of free ones
-- statement:
--   Let $G$ be a finite group, let $V$ be an abelian group that is free as a $\mathbb{Z}$-module, and let $\rho$ be a representation of $G$ on $V$ over $\mathbb{Z}$, viewed as the object $A =$ `Rep.of ρ` of $\mathrm{Rep}_{\mathbb{Z}}(G)$. Assume that for every subgroup $S \le G$ and every $q \in \mathbb{Z}$ the $\mathbb{Z}$-module $(\mathrm{Res}_S A)^{\wedge}{}^q$, that is `tateCohomology q` of the restriction of $A$ along the inclusion $S \hookrightarrow G$, is a zero object; here `tateCohomology` is $H^{n+1}(S,-)$ in degrees $q = n+1 \ge 1$, the quotient of the $S$-invariants by the range of the map `normBar` of the restricted representation in degree $0$, the kernel of `normBar` in degree $-1$, and $H_{n+1}(S,-)$ in degrees $q = -(n+2)$. The conclusion is that there exist a type $\alpha$ and morphisms $i : A \to$ `Rep.free ℤ G α` and $r :$ `Rep.free ℤ G α` $\to A$ of representations with $i$ followed by $r$ equal to the identity of $A$, i.e. $A$ is a retract of a free $\mathbb{Z}[G]$-module.
--
--   This is the classical criterion that a $G$-module which is $\mathbb{Z}$-free and cohomologically trivial for all subgroups is projective over $\mathbb{Z}[G]$, stated in the retract form used by its consumers. It feeds [`Rep.exists_shortExact_free_of_forall_isZero`](thm.html#Rep.exists_shortExact_free_of_forall_isZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_retract_free_of_forall_isZero.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.exists_retract_free_of_forall_isZero {G : Type} [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] (ρ : Representation ℤ G V)
    (hA : ∀ (S : Subgroup G) [Fintype S] (q : ℤ),
      CategoryTheory.Limits.IsZero ((Rep.res S.subtype (Rep.of ρ)).tateCohomology q)) :
    ∃ (α : Type) (i : Rep.of ρ ⟶ Rep.free ℤ G α) (r : Rep.free ℤ G α ⟶ Rep.of ρ), i ≫ r = 𝟙 (Rep.of ρ) := by sorry
