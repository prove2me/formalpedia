-- Prove2me | Theorems.Thm_TwinWidthI_MinorFree_twinWidth_components
-- name    : TwinWidthI.MinorFree.twinWidth_components
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:39.06581+00:00
-- url     : https://prove2.me/theorems/7e556b94-e40e-4227-a117-50dbaaaf8331
-- title:
--   p. 3:26 — twin-width is the maximum over connected components
-- statement:
--   Let $G$ be a finite graph and $d$ a nonnegative integer. Then $G$ has twin-width at most $d$ exactly when every connected component of $G$, with its induced graph, has twin-width at most $d$:
--
--   $$
--   \operatorname{tww}(G)\le d\quad\Longleftrightarrow\quad
--   \forall C\in\operatorname{Comp}(G),\ \operatorname{tww}(G[C])\le d.
--   $$
--
--   This permits the excluded-minor argument to work component by component. The empty graph is included; its contraction sequence ends at the empty partition.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:26, proof of Theorem 6.3, first paragraph

import Mathlib
import Definitions.Def_TwinWidthI_MinorFree_Setting

namespace TwinWidthI.MinorFree

/-- The twin-width of a graph is the maximum of that of its connected components (p. 3:26). -/
theorem twinWidth_components {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) :
    TwinWidthI.BoolWidth.TwinWidthLE G d ↔
      ∀ c : G.ConnectedComponent,
        letI : Fintype c.supp := Fintype.ofFinite c.supp
        letI : DecidableEq c.supp := Classical.decEq c.supp
        TwinWidthI.BoolWidth.TwinWidthLE (G.induce c.supp) d := by sorry

end TwinWidthI.MinorFree
