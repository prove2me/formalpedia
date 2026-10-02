-- Prove2me | Theorems.Thm_TeschlODE_IntervalMaps_shift_exists_dense_orbit
-- name    : TeschlODE.IntervalMaps.shift_exists_dense_orbit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T18:56:00.496905+00:00
-- url     : https://prove2.me/theorems/f892f823-c2f4-4d25-a86a-db46506d7c62
-- title:
--   Lemma 11.9 — the shift on Σ_N has a dense forward orbit
-- statement:
--   Let $N \ge 2$ and $\sigma$ the shift on $\Sigma_N$. There is $x \in \Sigma_N$ whose forward orbit $\{\sigma^k(x) : k \in \mathbb{N}_0\}$ is dense for the metric (11.28):
--   $$\exists x\ \forall y \in \Sigma_N\ \forall \varepsilon > 0\ \exists k \in \mathbb{N}_0:\ d(y, \sigma^k(x)) < \varepsilon .$$
--
--   **Formalization Note.** Density is stated metrically with $d$ = `symDist N`; the forward orbit (10.13) includes $k = 0$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 303, Lemma 11.9

import Mathlib
import Definitions.Def_TeschlODE_Shared_shift
import Definitions.Def_TeschlODE_Shared_symDist

namespace TeschlODE.IntervalMaps

/-- Teschl, Lemma 11.9, p. 303: the shift map `σ` on `Σ_N` (`N ≥ 2`) has a dense forward orbit:
there is an `x ∈ Σ_N` whose forward orbit `γ₊(x) = {σᵏ(x) | k ∈ ℕ₀}` (10.13) is dense with
respect to the metric (11.28). -/
theorem shift_exists_dense_orbit (N : ℕ) (hN : 2 ≤ N) :
    ∃ x : ℕ → Fin N, ∀ y : ℕ → Fin N, ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, TeschlODE.Shared.symDist N y ((TeschlODE.Shared.shift (N := N))^[k] x) < ε := by sorry

end TeschlODE.IntervalMaps
