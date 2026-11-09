-- Prove2me | Theorems.Thm_TermCycDich_all_red_grid
-- name    : TermCycDich.all_red_grid
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:46:20.645651+00:00
-- url     : https://prove2.me/theorems/d1e6e72a-6c1e-4173-a8bb-7a957f3a43b8
-- title:
--   Proof of Theorem 1.1 — $\Gamma_{c+1}$ is planar and $\mathrm{bidim}(\Gamma_{c+1}, V(\Gamma_{c+1})) = c+1$
-- statement:
--   For every integer $c\ge0$, the $((c+1)\times(c+1))$-grid $\Gamma_{c+1}$ is planar, and with all of its vertices red it has bidimensionality exactly $c+1$:
--
--   $$
--   \mathrm{bidim}\bigl(\Gamma_{c+1}, V(\Gamma_{c+1})\bigr)=c+1.
--   $$
--
--   Hence a class of bidimensionality at most $c$ misses the annotated planar graph $(\Gamma_{c+1}, V(\Gamma_{c+1}))$.
--
--   Differences from the source:
--   - encoding: the grid Γ_{c+1} → the public RobertsonSeymour1986.GM5.grid (c + 1) on Fin (c+1) × Fin (c+1), all vertices red (Set.univ); reason: Lean convention; same graph
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), proof of Theorem 1.1, p.67 (PDF 69)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
import Definitions.Def_RobertsonSeymour1986_GM5_grid
import Definitions.Def_TermCycDich_bidim

namespace TermCycDich

/-- **The all-red grid**: for every `c`, the grid `Γ_{c+1}` is planar, and with all vertices red
it has bidimensionality exactly `c + 1`.

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), proof of Theorem 1.1, p.67 (PDF 69): "First, Γ_{c+1}, in which all vertices are red, is
planar and has bidimensionality c+1."

**Formalization Note** `Γ_{c+1}` is the public `RobertsonSeymour1986.GM5.grid (c + 1)`; planarity
is `RobertsonSeymour1986.GM5.IsPlanar`. -/
theorem all_red_grid (c : ℕ) :
    RobertsonSeymour1986.GM5.IsPlanar (RobertsonSeymour1986.GM5.grid (c + 1)) ∧
      bidim (RobertsonSeymour1986.GM5.grid (c + 1)) Set.univ = c + 1 := by sorry

end TermCycDich
