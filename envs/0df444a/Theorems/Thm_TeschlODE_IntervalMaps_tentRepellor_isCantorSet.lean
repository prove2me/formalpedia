-- Prove2me | Theorems.Thm_TeschlODE_IntervalMaps_tentRepellor_isCantorSet
-- name    : TeschlODE.IntervalMaps.tentRepellor_isCantorSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T18:58:47.563583+00:00
-- url     : https://prove2.me/theorems/3ce94903-1734-4f9f-85cd-3236e56b187f
-- title:
--   Lemma 11.4 — for µ > 2 the invariant set Λ of the tent map is a Cantor set
-- statement:
--   Let $\mu > 2$ and let $\Lambda = \{x \in \mathbb{R} : T_\mu^n(x) \in [0,1]\ \forall n \ge 0\}$ be the set of points whose orbit under the tent map stays in $[0,1]$ (the book's $\bigcap_n \Lambda_n$, (11.18)). Then $\Lambda$ is a Cantor set: compact, totally disconnected, and perfect.
--
--   **Formalization Note.** $\mu > 2$ is the standing assumption of §11.4 (p. 298).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 299, Lemma 11.4

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentRepellor
import Definitions.Def_TeschlODE_IntervalMaps_IsCantorSet

namespace TeschlODE.IntervalMaps

/-- Teschl, Lemma 11.4, p. 299: for the tent map `T_µ` with `µ > 2` (the standing assumption of
§11.4), the set `Λ` (11.18) of points staying in `[0, 1]` under all iterations is a Cantor set:
compact, totally disconnected and perfect. -/
theorem tentRepellor_isCantorSet (μ : ℝ) (hμ : 2 < μ) :
    IsCantorSet (TeschlODE.Shared.tentRepellor μ) := by sorry

end TeschlODE.IntervalMaps
