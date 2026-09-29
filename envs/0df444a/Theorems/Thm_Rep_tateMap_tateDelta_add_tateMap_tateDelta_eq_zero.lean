-- Prove2me | Theorems.Thm_Rep_tateMap_tateDelta_add_tateMap_tateDelta_eq_zero
-- name    : Rep.tateMap_tateDelta_add_tateMap_tateDelta_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/97c18dd0-3dc1-5bf1-a50b-be08fbc2cf75
-- title:
--   Compatible pairings annihilate the sum of Tate connecting maps
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, and let $X$ and $Y$ be short complexes $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$, $Y_1 \xrightarrow{f'} Y_2 \xrightarrow{g'} Y_3$ in the category of $k$-linear representations of $G$, both assumed short exact (`hX`, `hY`). Assume further that the short complex obtained from $X$ by tensoring on the right with $Y_3$ is short exact (`hR`), and that the one obtained from $Y$ by tensoring on the left with $X_3$ is short exact (`hC`). Let $D$ be a representation and let $\varphi : X_2 \otimes Y_2 \to D$, $\varphi' : X_1 \otimes Y_3 \to D$, $\varphi'' : X_3 \otimes Y_1 \to D$ be morphisms of representations satisfying the two compatibilities $(f \otimes 1_{Y_2})$ followed by $\varphi$ equals $(1_{X_1} \otimes g')$ followed by $\varphi'$, and $(1_{X_2} \otimes f')$ followed by $\varphi$ equals $(g \otimes 1_{Y_1})$ followed by $\varphi''$. Then for every $n \in \mathbb{Z}$ and every class $w$ in the Tate cohomology $\hat H^n(G, X_3 \otimes Y_3)$ — which by definition is $H^n$ of the group for $n \ge 1$, the invariants modulo the range of the norm map for $n = 0$, the kernel of the norm map on coinvariants for $n = -1$, and $H_{-n-1}$ of the group for $n \le -2$ — the sum of the image of $\delta_{\mathrm{hR}}(w)$ under the map induced by $\varphi'$ and the image of $\delta_{\mathrm{hC}}(w)$ under the map induced by $\varphi''$ vanishes in $\hat H^{n+1}(G, D)$, where $\delta$ denotes the connecting map [`Rep.tateδ`](def/GroupCohomology_TateShiftMaps.html#L32) of the indicated short exact sequence and induced maps are those given by [`Rep.tateMap`](def/GroupCohomology_TateShiftMaps.html#L17) (group cohomology functoriality, the map on invariants modulo norms, the map on the kernel of the norm, and group homology functoriality, according to the sign of the degree).
--
--   This is the pairing-free form of the classical anticommutation rule $\delta(x) \cup y + (-1)^p\, x \cup \delta(y) = 0$ for Tate cohomology of two short exact sequences paired compatibly into a third module. It is used in the treatment of Tate cup products, being cited by [`Rep.IsTateCupProduct.cupEv_characterDual_eq_zero`](thm.html#Rep.IsTateCupProduct.cupEv_characterDual_eq_zero) and [`Rep.IsTateCupProduct.injective_cupEv_characterDual`](thm.html#Rep.IsTateCupProduct.injective_cupEv_characterDual) on the way to duality statements for the pairing with the character dual.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_tateMap_tateDelta_add_tateMap_tateDelta_eq_zero.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.tateMap_tateDelta_add_tateMap_tateDelta_eq_zero {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X Y : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (hY : Y.ShortExact)
    (hR : (X.map (MonoidalCategory.tensorRight Y.X₃)).ShortExact)
    (hC : (Y.map (MonoidalCategory.tensorLeft X.X₃)).ShortExact)
    {D : Rep.{u} k G} (φ : X.X₂ ⊗ Y.X₂ ⟶ D) (φ' : X.X₁ ⊗ Y.X₃ ⟶ D) (φ'' : X.X₃ ⊗ Y.X₁ ⟶ D)
    (h' : X.f ▷ Y.X₂ ≫ φ = X.X₁ ◁ Y.g ≫ φ') (h'' : X.X₂ ◁ Y.f ≫ φ = X.g ▷ Y.X₁ ≫ φ'')
    (n : ℤ) (w : (X.X₃ ⊗ Y.X₃).tateCohomology n) :
    (Rep.tateMap φ' (n + 1)).hom ((Rep.tateδ hR n).hom w)
      + (Rep.tateMap φ'' (n + 1)).hom ((Rep.tateδ hC n).hom w) = 0 := by sorry
