-- Prove2me | Theorems.Thm_Rep_tateDelta_comp_tateDelta_eq_neg
-- name    : Rep.tateDelta_comp_tateDelta_eq_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/7446159a-5a85-5f27-92a8-126b0488bfd8
-- title:
--   Anticommutativity of Tate connecting maps in a 3× 3 diagram
-- statement:
--   Fix a universe, a commutative ring $k$ and a finite group $G$, and let $X$ and $Y$ be short complexes of $k$-linear representations of $G$, with terms $X_1 \to X_2 \to X_3$ and $Y_1 \to Y_2 \to Y_3$. Six exactness hypotheses are imposed: for each $j \in \{1,2,3\}$ the short complex obtained by applying the functor $-\otimes Y_j$ to $X$ is short exact (hypotheses `hR₁`, `hR₂`, `hR₃`), and for each $i \in \{1,2,3\}$ the short complex obtained by applying $X_i \otimes -$ to $Y$ is short exact (hypotheses `hC₁`, `hC₂`, `hC₃`). For an integer $n$ and such a short exact short complex, [`Rep.tateδ`](def/GroupCohomology_TateShiftMaps.html#L32) denotes the associated degree-$n$ Tate connecting morphism, going from Tate cohomology in degree $n$ of the third term to Tate cohomology in degree $n+1$ of the first term. The conclusion is the identity of morphisms $\hat H^{n}(G, X_3 \otimes Y_3) \to \hat H^{n+2}(G, X_1 \otimes Y_1)$ asserting that the connecting map of the rows tensored with $Y_3$ in degree $n$, followed by the connecting map of the columns tensored with $X_1$ in degree $n+1$, equals the negative of the connecting map of the columns tensored with $X_3$ in degree $n$ followed by the connecting map of the rows tensored with $Y_1$ in degree $n+1$. The middle hypotheses `hR₂` and `hC₂` are part of the stated data.
--
--   This is the anticommutativity of the two ways of traversing a $3\times 3$ diagram of short exact sequences of representations by Tate connecting maps, the sign rule that makes the iterated connecting map well defined up to sign in all degrees. It is used in the construction of the Tate cup product, [`Rep.exists_isTateCupProduct`](thm.html#Rep.exists_isTateCupProduct).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_tateDelta_comp_tateDelta_eq_neg.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_TateShiftMaps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.tateDelta_comp_tateDelta_eq_neg {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X Y : ShortComplex (Rep.{u} k G)}
    (hR₁ : (X.map (MonoidalCategory.tensorRight Y.X₁)).ShortExact)
    (hR₂ : (X.map (MonoidalCategory.tensorRight Y.X₂)).ShortExact)
    (hR₃ : (X.map (MonoidalCategory.tensorRight Y.X₃)).ShortExact)
    (hC₁ : (Y.map (MonoidalCategory.tensorLeft X.X₁)).ShortExact)
    (hC₂ : (Y.map (MonoidalCategory.tensorLeft X.X₂)).ShortExact)
    (hC₃ : (Y.map (MonoidalCategory.tensorLeft X.X₃)).ShortExact) (n : ℤ) :
    Rep.tateδ hR₃ n ≫ Rep.tateδ hC₁ (n + 1) = -(Rep.tateδ hC₃ n ≫ Rep.tateδ hR₁ (n + 1)) := by sorry
