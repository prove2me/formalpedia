-- Prove2me | Theorems.Thm_SteinerShortcuts_Main_construction_shortcut_tradeoff
-- name    : SteinerShortcuts.Main.construction_shortcut_tradeoff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T17:15:00.788653+00:00
-- url     : https://prove2.me/theorems/743f576d-bdee-47ad-ad7e-a6656c668964
-- title:
--   Finite construction shortcut charging bound
-- statement:
--   Let $L\ge4$ be even and let $q\in[L,2L]$ be prime. For the construction of Section 3.2, write $\mathcal P$ for its critical paths. Every finite reachability-preserving Steiner augmentation with added edge set $E^+$ and finite-distance diameter $D$ satisfies
--
--   $$D\ge1,\qquad |\mathcal P|\left\lfloor\frac{L-1}{D+1}\right\rfloor\le |E^+|.$$
--
--   This finite counting inequality supplies the size–diameter tradeoff used to prove Theorem 1.3.
-- source:
--   Bernstein et al., Polynomial Lower Bounds for Steiner Shortcuts via Test Functions, STOC 2027 submission #1034, proof of Theorem 1.3, printed pp. 23–24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_Construction
open SteinerShortcuts.Main

theorem SteinerShortcuts.Main.construction_shortcut_tradeoff (L q : ℕ) (h : Admissible L q) (W : Type) [Fintype W]
    (extra : Finset ((Vertex L q ⊕ W) × (Vertex L q ⊕ W)))
    (he : IsSteinerShortcut (finiteConstruction L q) extra) :
    1 ≤ diameter (augment (finiteConstruction L q) extra) ∧
      (criticalPaths L q).card * ((L-1)/(diameter (augment (finiteConstruction L q) extra)+1)) ≤ extra.card := by sorry
