-- Prove2me | Theorems.Thm_SEF_zero_free_region_vinogradov_korobov
-- name    : SEF.zero_free_region_vinogradov_korobov
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-22T20:01:24.547375+00:00
-- url     : https://prove2.me/theorems/7c7d288b-5346-4ee5-8d79-a09cab256a1b
-- title:
--   The Vinogradov-Korobov zero-free region, the strongest published for the Riemann zeta function
-- statement:
--   There is an absolute positive real constant c such that the Riemann zeta function does not vanish at any complex number sigma + i t with |t| >= 3 whose real part sigma satisfies sigma >= 1 - c / ((log |t|)^(2/3) (log log |t|)^(1/3)). This is the zero-free region of Vinogradov and Korobov (1958), the strongest published zero-free region for the zeta function; the region approaches the line sigma = 1 only logarithmically, which is exactly the gap that the open seven-eighths statements of the mission address. The statement is drafted for this mission as a literature anchor; the citation is given in the item's source field.
-- source:
--   N. M. Korobov, Estimates of trigonometric sums and their applications, Uspekhi Matematicheskikh Nauk 13 (1958) 185-192, the main theorem (the Vinogradov-Korobov zero-free region for the zeta function).

import Mathlib
import Definitions.Def_SEF_theta
import Definitions.Def_SEF_hecke

/-!
# SEF: the Vinogradov-Korobov zero-free region for the zeta function

There is an absolute constant $c > 0$ such that $\zeta(\sigma + it) \ne 0$
whenever $|t| \ge 3$ and
$\sigma \ge 1 - c / ((\log |t|)^{2/3} (\log \log |t|)^{1/3})$. This literature
milestone is the strongest published zero-free region for $\zeta$ (Vinogradov
and Korobov, 1958); the mission goals go strictly beyond it, since the region
approaches the line $\sigma = 1$ only logarithmically. The Lean statement is
drafted for this mission (there is no source file for it); the citation is
given in the item's source field. Proved in the literature; draft: the proof
is a `sorry`.
-/

namespace SEF

theorem zero_free_region_vinogradov_korobov :
    ∃ c : ℝ, 0 < c ∧
      ∀ σ t : ℝ, 3 ≤ |t| →
        1 - c / ((Real.log |t|) ^ (2 / 3 : ℝ) * (Real.log (Real.log |t|)) ^ (1 / 3 : ℝ)) ≤ σ →
          riemannZeta ⟨σ, t⟩ ≠ 0 := by
  sorry

end SEF
