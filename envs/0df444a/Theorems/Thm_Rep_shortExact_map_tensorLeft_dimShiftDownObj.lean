-- Prove2me | Theorems.Thm_Rep_shortExact_map_tensorLeft_dimShiftDownObj
-- name    : Rep.shortExact_map_tensorLeft_dimShiftDownObj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/8180c9f8-a217-5b35-a0dd-a8c5a5620f5a
-- title:
--   Left tensoring by the dimension-shift subobject preserves short exactness
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $X$ a short complex $X_1 \to X_2 \to X_3$ in the category $\mathrm{Rep}\,k\,G$ of $k$-linear representations of $G$, and $A$ a representation. Write $\mathrm{indBot}\,A = \mathrm{ind}\,(\bot \hookrightarrow G)\,(\mathrm{res}\,(\bot \hookrightarrow G)\,A)$ for the representation induced from the restriction of $A$ to the trivial subgroup, and let $A.\mathrm{dimShiftDownObj}$ be the subrepresentation of $\mathrm{indBot}\,A$ carried by the kernel of the underlying $k$-linear map of the morphism [`Rep.indBotπ A`](def/GroupCohomology_TateDimensionShift.html#L27) (a $G$-stable submodule, since that kernel is preserved by the action). The hypothesis is that the short complex obtained from $X$ by applying the functor $A \otimes (-)$, i.e. `MonoidalCategory.tensorLeft A`, is short exact: $0 \to A \otimes X_1 \to A \otimes X_2 \to A \otimes X_3 \to 0$. The conclusion is that the short complex obtained from $X$ by applying $A.\mathrm{dimShiftDownObj} \otimes (-)$ is likewise short exact, i.e. the first map is a monomorphism, the second an epimorphism, and the complex is exact in the middle.
--
--   This is the flatness-type input needed for Tate dimension shifting: the down-shift object $A'' = \ker(\mathrm{Ind}_{1}^{G}\mathrm{Res}\,A \to A)$ inherits from $A$ the property that tensoring a short exact sequence with it stays short exact. It feeds the construction of Tate cup products, being used in [`Rep.exists_isTateCupProduct`](thm.html#Rep.exists_isTateCupProduct), and is the left-handed counterpart of the corresponding statement for tensoring on the right.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_shortExact_map_tensorLeft_dimShiftDownObj.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.shortExact_map_tensorLeft_dimShiftDownObj {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (A : Rep.{u} k G) (hAX : (X.map (MonoidalCategory.tensorLeft A)).ShortExact) :
    (X.map (MonoidalCategory.tensorLeft A.dimShiftDownObj)).ShortExact := by sorry
