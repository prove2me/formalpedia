-- Prove2me | Theorems.Thm_ReentrantScheduling_LBFS_eq14_recursion
-- name    : ReentrantScheduling.LBFS.eq14_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:08.924298+00:00
-- url     : https://prove2.me/theorems/d0decd44-c530-4c24-b159-cc4bf346bc3a
-- title:
--   (14), p. 1412 — $x(t_k)\le(\lambda c(\varepsilon)+\gamma)+\lambda(\overline w+\varepsilon)x(t_{k-1})$
-- statement:
--   Consider an LBFS-admissible run of a nonacyclic flow line whose arrivals satisfy (1) with constants $\lambda, \gamma \ge 0$. Let $t_0 \ge 0$ and let $\pi$ be the part at the *beginning* of the system at time $t_0$: a part in the system at $t_0$ that comes last in line order among them. Then $\pi$ exits at a finite time $t_1 = e(\pi)$, and for every $\varepsilon > 0$
--
--   $$
--   x(t_1) \le \big(\lambda c(\varepsilon) + \gamma\big) + \lambda(\overline w + \varepsilon)\, x(t_0), \qquad (14)
--   $$
--
--   where $x(t)$ is the number of parts in the system at time $t$ and $c(\varepsilon) = c^{(1)}(\varepsilon)$ is the constant of Theorem 2.
--
--   Iterating (14) along the exit times $t_0 < t_1 < t_2 < \cdots$ of the successive parts at the beginning of the system shows, when $\rho = \lambda\overline w < 1$ and $\varepsilon$ is small, that $x(t_k)$ is eventually at most $(\lambda c(\varepsilon) + \gamma)/(1 - \rho - \lambda\varepsilon)$.
--
--   **Formalization Note.** The inequality is in $[0, \infty]$, since $x$ is a cardinality. The case of an empty system at $t_0$, which the page leaves to the reader, is excluded by assuming $\pi$ exists. The load condition (3) is not needed for (14).
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, p. 1412, proof of Theorem 3, (14)

import Mathlib
import Definitions.Def_ReentrantScheduling_LBFS_Model
import Definitions.Def_ReentrantScheduling_LBFS_Constants

namespace ReentrantScheduling.LBFS

/-- The recursion (14), p. 1412: under LBFS and (1), let `π` be the part at the beginning of
the system at time `t₀ ≥ 0` (the last part in line order among those in the system). Then
`π` exits at a finite time `t₁`, and `x(t₁) ≤ (λ c(ε) + γ) + λ (w̄ + ε) x(t₀)` for every
`ε > 0`. -/
theorem eq14_recursion (L : Line) (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ)
    (R : Run L) (hR : R.Admissible L.lbfsPrio) (hA : R.Arrivals lam γ)
    (ε : ℝ) (hε : 0 < ε) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (π : R.Part) (hπ : R.inSystem π t₀)
    (hbeg : ∀ q, R.inSystem q t₀ → R.ord q ≤ R.ord π) :
    ∃ t₁ : ℝ, R.exit π = (t₁ : WithTop ℝ) ∧
      ((R.x t₁ : ℕ∞) : ENNReal) ≤ ENNReal.ofReal (lam * L.cLBFS ε + γ) +
        ENNReal.ofReal (lam * (L.wbar + ε)) * ((R.x t₀ : ℕ∞) : ENNReal) := by sorry

end ReentrantScheduling.LBFS
