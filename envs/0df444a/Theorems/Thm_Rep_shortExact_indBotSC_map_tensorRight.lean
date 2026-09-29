-- Prove2me | Theorems.Thm_Rep_shortExact_indBotSC_map_tensorRight
-- name    : Rep.shortExact_indBotSC_map_tensorRight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/c457bdb0-8346-5af1-9749-56d4ea704a8d
-- title:
--   Tensoring the dimension-shift induction preserves short exactness
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, let $X$ be a short complex $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ in the category of $k$-linear representations of $G$, and let $B$ be such a representation. Assume that the short complex obtained from $X$ by applying the functor $- \otimes B$ termwise, namely $X_1 \otimes B \to X_2 \otimes B \to X_3 \otimes B$, is short exact (the first map a monomorphism, the second an epimorphism, and the complex exact at the middle term). The conclusion is that the same holds after first replacing $X$ by [`Rep.indBotSC X`](def/GroupCohomology_TateDimensionShiftMaps.html#L56): this is the short complex whose terms are the representations $(X_i)$ induced up from the trivial subgroup after restriction to it, i.e. the image of $X_i$ under `Rep.indFunctor k (⊥ : Subgroup G).subtype` applied to its restriction along $(⊥ : Subgroup G).subtype$, and whose maps are [`Rep.indBotMap X.f`](def/GroupCohomology_TateDimensionShiftMaps.html#L17) and [`Rep.indBotMap X.g`](def/GroupCohomology_TateDimensionShiftMaps.html#L17), the corresponding induced maps (the composite of the two maps being zero by functoriality). Thus the short complex $(X_1)_{\flat} \otimes B \to (X_2)_{\flat} \otimes B \to (X_3)_{\flat} \otimes B$, with $(\,\cdot\,)_{\flat}$ the induction from the trivial subgroup, is again short exact. No exactness or other hypothesis on $X$ itself is required, only on $X \otimes B$.
--
--   This is the compatibility of the dimension-shifting construction $A \mapsto \mathrm{Ind}_{\{1\}}^{G}\mathrm{Res}_{\{1\}} A$ with tensoring by a fixed representation, at the level of short exact sequences; the underlying point is the functorial untwisting isomorphism $\mathrm{Ind}_{\{1\}}^{G}\mathrm{Res}_{\{1\}}(A) \otimes B \cong (G \to_0 k) \otimes_k (A \otimes B)$ with trivial action on the second factor. It is used in the construction of Tate cup products, via [`Rep.exists_isTateCupProduct`](thm.html#Rep.exists_isTateCupProduct), where dimension shifts must be performed inside a sequence that remains exact after tensoring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_shortExact_indBotSC_map_tensorRight.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_TateDimensionShiftMaps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.shortExact_indBotSC_map_tensorRight {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (B : Rep.{u} k G) (hXB : (X.map (MonoidalCategory.tensorRight B)).ShortExact) :
    ((Rep.indBotSC X).map (MonoidalCategory.tensorRight B)).ShortExact := by sorry
