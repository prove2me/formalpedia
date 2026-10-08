-- Prove2me | Theorems.Thm_ReentrantScheduling_LBFS_theorem3_lbfs_bounded
-- name    : ReentrantScheduling.LBFS.theorem3_lbfs_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:21.107595+00:00
-- url     : https://prove2.me/theorems/bd667e42-e544-4ca5-8224-cec534d546ed
-- title:
--   Theorem 3, p. 1412 — under LBFS, $x(t)$ stays bounded and $\limsup x(t)\le(\lambda c(\varepsilon)+\gamma)/(1-\rho-\lambda\varepsilon)$
-- statement:
--   **Stability of LBFS.** Consider a nonacyclic flow line operated under the last buffer first serve policy. Suppose the arrivals satisfy (1) with constants $\lambda, \gamma \ge 0$ and the arrival rate satisfies the capacity condition $\rho = \lambda \overline w < 1$ (3). Let $x(t)$ be the number of parts in the system at time $t$, and $x(0)$ the number in the system at time $0$. Then for every $\varepsilon > 0$ small enough that $1 - \rho - \lambda\varepsilon > 0$:
--
--   1. for all $t \ge 0$,
--   $$
--   x(t) \le \max\Big\{ (1 + \rho + \lambda\varepsilon)\, x(0) + \lambda c(\varepsilon) + \gamma,\ \frac{2(\lambda c(\varepsilon) + \gamma)}{1 - \rho - \lambda\varepsilon} \Big\},
--   $$
--   which bounds the transient behavior;
--   2. $$
--   \limsup_{t \to \infty} x(t) \le \frac{\lambda c(\varepsilon) + \gamma}{1 - \rho - \lambda\varepsilon},
--   $$
--   which bounds the asymptotic behavior.
--
--   Here $c(\varepsilon) = c^{(1)}(\varepsilon)$ is the explicit constant of Theorem 2. The first bound depends on the initial state; the second does not. The theorem holds for every admissible LBFS run, including runs with simultaneous arrivals and with parts already in service at time $0$.
--
--   **Formalization Note.** The page prints ii) as $\lambda c(\varepsilon) + \gamma/(1 - \rho - \lambda\varepsilon)$; the proof's final display, and the second branch of i), give $(\lambda c(\varepsilon) + \gamma)/(1 - \rho - \lambda\varepsilon)$, which is what is stated here. Both bounds are inequalities in $[0, \infty]$ (`ENNReal`), and the $\limsup$ is the `ENNReal` limit superior along $t \to \infty$, so no boundedness side condition can make it vacuous. $x(0)$ counts every part in the system at time $0$, including parts released at time $0$.
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, p. 1412, Theorem 3; proof p. 1412

import Mathlib
import Definitions.Def_ReentrantScheduling_LBFS_Model
import Definitions.Def_ReentrantScheduling_LBFS_Constants

namespace ReentrantScheduling.LBFS

/-- Theorem 3 (Stability of LBFS), p. 1412: under LBFS, arrivals satisfying (1) and load
`ρ < 1` (3), for every `ε > 0` with `1 − ρ − λε > 0`:
i) `x(t) ≤ max {(1 + ρ + λε) x(0) + λc(ε) + γ, 2(λc(ε) + γ)/(1 − ρ − λε)}` for all `t ≥ 0`;
ii) `limsup_{t→∞} x(t) ≤ (λc(ε) + γ)/(1 − ρ − λε)` (the page prints `λc(ε) + γ/(1 − ρ − λε)`;
the proof establishes the bracketed form). -/
theorem theorem3_lbfs_bounded (L : Line) (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ)
    (hload : L.load lam < 1) (R : Run L) (hR : R.Admissible L.lbfsPrio)
    (hA : R.Arrivals lam γ) (ε : ℝ) (hε : 0 < ε) (hgap : 0 < 1 - L.load lam - lam * ε) :
    (∀ t : ℝ, 0 ≤ t → ((R.x t : ℕ∞) : ENNReal) ≤
        max (ENNReal.ofReal (1 + L.load lam + lam * ε) * ((R.x 0 : ℕ∞) : ENNReal) +
              ENNReal.ofReal (lam * L.cLBFS ε + γ))
          (ENNReal.ofReal (2 * (lam * L.cLBFS ε + γ) / (1 - L.load lam - lam * ε)))) ∧
    Filter.limsup (fun t : ℝ => ((R.x t : ℕ∞) : ENNReal)) Filter.atTop ≤
      ENNReal.ofReal ((lam * L.cLBFS ε + γ) / (1 - L.load lam - lam * ε)) := by sorry

end ReentrantScheduling.LBFS
