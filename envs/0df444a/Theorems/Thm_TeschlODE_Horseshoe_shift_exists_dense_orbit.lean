-- Prove2me | Theorems.Thm_TeschlODE_Horseshoe_shift_exists_dense_orbit
-- name    : TeschlODE.Horseshoe.shift_exists_dense_orbit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T06:11:53.934591+00:00
-- url     : https://prove2.me/theorems/bdf71321-b847-41e5-ae7a-ae8ab3355214
-- title:
--   Lemma 11.9 — the shift on $\Sigma_N$ has a dense forward orbit
-- statement:
--   Let $N \ge 2$ and let $\sigma$ be the shift on the one-sided space $\Sigma_N$ with the metric (11.28). There is a sequence $x \in \Sigma_N$ whose forward orbit is dense:
--   $$\forall y \in \Sigma_N,\ \forall \varepsilon > 0,\ \exists k \in \mathbb{N}_0:\quad d\bigl(y, \sigma^k(x)\bigr) < \varepsilon.$$
--   A dense forward orbit gives topological transitivity (Problem 11.3), the second ingredient of chaos.
--
--   **Formalization Note.** A single $x$ serves all $y$ and $\varepsilon$: the existential comes first. The orbit includes $k = 0$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 303, Lemma 11.9

import Mathlib
import Definitions.Def_TeschlODE_Shared_shift
import Definitions.Def_TeschlODE_Shared_symDist

namespace TeschlODE.Horseshoe

/-- Teschl, Lemma 11.9, p. 303: the shift map `σ` on the one-sided space `Σ_N` (`N ≥ 2`) has a
dense forward orbit: there is an `x ∈ Σ_N` whose forward orbit `{σᵏ(x) | k ∈ ℕ₀}` is dense
with respect to the metric (11.28). -/
theorem shift_exists_dense_orbit (N : ℕ) (hN : 2 ≤ N) :
    ∃ x : ℕ → Fin N, ∀ y : ℕ → Fin N, ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, TeschlODE.Shared.symDist N y ((TeschlODE.Shared.shift (N := N))^[k] x) < ε := by sorry

end TeschlODE.Horseshoe
