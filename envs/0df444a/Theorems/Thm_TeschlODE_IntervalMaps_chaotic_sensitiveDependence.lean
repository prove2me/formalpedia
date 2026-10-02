-- Prove2me | Theorems.Thm_TeschlODE_IntervalMaps_chaotic_sensitiveDependence
-- name    : TeschlODE.IntervalMaps.chaotic_sensitiveDependence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T18:46:10.730989+00:00
-- url     : https://prove2.me/theorems/8e51848b-8363-432f-ad77-d5ea53865374
-- title:
--   Lemma 11.3 — a chaotic system has sensitive dependence on initial conditions
-- statement:
--   Let $(M, d)$ be a metric space and $f : M \to M$ chaotic: $f$ continuous, $M$ infinite, $f$ topologically transitive, and the periodic points of $f$ dense in $M$. Then $f$ exhibits sensitive dependence on initial conditions: there is $\delta > 0$ such that
--   $$\forall x \in M\ \forall \varepsilon > 0\ \exists y \in M\ \exists n \ge 1:\quad d(x,y) < \varepsilon,\quad d(f^n(x), f^n(y)) > \delta .$$
--   It justifies dropping the sensitivity clause from the definition of chaos.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 297, Lemma 11.3

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsChaotic
import Definitions.Def_TeschlODE_IntervalMaps_SensitiveDependence

namespace TeschlODE.IntervalMaps

/-- Teschl, Lemma 11.3, p. 297: if `f : M → M` on a metric space `M` is chaotic (continuous,
`M` infinite, topologically transitive, periodic points dense; p. 296), then it exhibits
sensitive dependence on initial conditions (pp. 295–296). -/
theorem chaotic_sensitiveDependence {M : Type*} [MetricSpace M] (f : M → M)
    (hf : TeschlODE.Shared.IsChaotic f) : SensitiveDependence f := by sorry

end TeschlODE.IntervalMaps
