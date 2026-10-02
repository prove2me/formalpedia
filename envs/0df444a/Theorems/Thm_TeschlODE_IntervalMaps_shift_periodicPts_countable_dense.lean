-- Prove2me | Theorems.Thm_TeschlODE_IntervalMaps_shift_periodicPts_countable_dense
-- name    : TeschlODE.IntervalMaps.shift_periodicPts_countable_dense
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T18:50:57.630583+00:00
-- url     : https://prove2.me/theorems/1926e541-953f-4779-86d8-6c27a3ad7ca1
-- title:
--   Lemma 11.8 — the shift on Σ_N has countably many periodic points, and they are dense
-- statement:
--   Let $N \ge 2$ and $\sigma$ the shift on $\Sigma_N$. The set $\mathrm{Per}(\sigma) = \{x : \sigma^n(x) = x \text{ for some } n \ge 1\}$ is countable, and it is dense for the metric (11.28):
--   $$\forall x \in \Sigma_N\ \forall \varepsilon > 0\ \exists p \in \mathrm{Per}(\sigma):\ d(p, x) < \varepsilon .$$
--   Together with Lemma 11.9 this shows that $(\Sigma_N, \sigma)$ is chaotic.
--
--   **Formalization Note.** Density is stated metrically with $d$ = `symDist N`, not through a topology instance on $\Sigma_N$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 303, Lemma 11.8

import Mathlib
import Definitions.Def_TeschlODE_Shared_shift
import Definitions.Def_TeschlODE_Shared_symDist

namespace TeschlODE.IntervalMaps

/-- Teschl, Lemma 11.8, p. 303: the shift map `σ` on `Σ_N` (`N ≥ 2`) has a countable number of
periodic points (`Per(σ) = {x | σⁿ(x) = x for some n ≥ 1}`), and they are dense with respect to
the metric (11.28): every `x ∈ Σ_N` is within any `ε > 0` of a periodic point. -/
theorem shift_periodicPts_countable_dense (N : ℕ) (hN : 2 ≤ N) :
    (Function.periodicPts (TeschlODE.Shared.shift (N := N))).Countable ∧
      ∀ x : ℕ → Fin N, ∀ ε : ℝ, 0 < ε →
        ∃ p ∈ Function.periodicPts (TeschlODE.Shared.shift (N := N)), TeschlODE.Shared.symDist N p x < ε := by sorry

end TeschlODE.IntervalMaps
