-- Prove2me | Theorems.Thm_Rep_nonempty_twist_inv_twist_iso
-- name    : Rep.nonempty_twist_inv_twist_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/0912716f-cbd4-50c2-9718-51f26fdbb4b8
-- title:
--   Twisting by χ⁻¹ then by χ recovers a representation
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, let $N$ be an object of $\mathrm{Rep}_k(G)$ (a $k$-linear representation of $G$ on a $k$-module, taken in universe $0$), and let $\chi : G \to k^{\times}$ be a group homomorphism into the units of $k$. For a representation with underlying action $\rho$ and a character $\chi$, the twist is defined on the same underlying $k$-module by $g \mapsto (\chi g) \cdot \rho(g)$, where $(\chi g)$ denotes the image of the unit $\chi g$ in $k$ acting by scalar multiplication; [`Rep.twist`](def/GroupCohomology_Selmer.html#L38) packages this as an object of $\mathrm{Rep}_k(G)$ with the same carrier. The theorem asserts that the type of isomorphisms in $\mathrm{Rep}_k(G)$ from $(N \otimes \chi^{-1}) \otimes \chi$, that is from the twist by $\chi$ of the twist of $N$ by the pointwise inverse character $\chi^{-1}$, to $N$ is nonempty. Thus only the existence of such an isomorphism is asserted, not a designated one; the isomorphism produced is the identity on the common underlying $k$-module.
--
--   This is the elementary statement that twisting a representation by a character and by its inverse is inverse to each other, the twisting operation being unchanged on underlying modules. It is used as bookkeeping in the computation of continuous $H^2$ and its $k$-dimension for coinduced modules, in [`groupCohomology.finiteDimensional_continuousH2S_coind_and_finrank_eq`](thm.html#groupCohomology.finiteDimensional_continuousH2S_coind_and_finrank_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_nonempty_twist_inv_twist_iso.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation
open scoped Classical

theorem Rep.nonempty_twist_inv_twist_iso {k : Type} [CommRing k] {G : Type} [Group G] (N : Rep.{0} k G) (χ : G →* kˣ) :
    Nonempty ((N.twist χ⁻¹).twist χ ≅ N) := by sorry
