-- Prove2me | Theorems.Thm_SEF_siegel_ineffective
-- name    : SEF.siegel_ineffective
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-22T20:02:08.023308+00:00
-- url     : https://prove2.me/theorems/030927bc-837c-45c5-a20a-0c52617c1f4c
-- title:
--   Siegel's ineffective theorem for the real zeros of Dirichlet L-functions
-- statement:
--   For every positive real epsilon there is a positive real constant c depending only on epsilon such that, for every modulus q of at least 3, every primitive non-principal Dirichlet character chi mod q that takes real values, and every real beta with 0 < beta < 1 at which the L-function of chi vanishes, the inequality (1 - beta) q^epsilon <= c holds. This is Siegel's theorem (1935), the ineffective bound for the real zeros of Dirichlet L-functions lying closest to the line sigma = 1; the constant exists, but the proof provides no effective means of computing it. It is the literature anchor for the two logarithmic Siegel statements of the mission, which go strictly beyond it. The statement is drafted for this mission; the citation is given in the item's source field.
-- source:
--   C. L. Siegel, Über die Classenzahl quadratischer Zahlkörper, Acta Arithmetica 1 (1935) 83-86, the theorem of Section 2 (the real-zero estimate for Dirichlet L-functions).

import Mathlib
import Definitions.Def_SEF_theta
import Definitions.Def_SEF_hecke

/-!
# SEF: Siegel's ineffective theorem for real zeros

For every $\varepsilon > 0$ there is a constant $c(\varepsilon) > 0$ such
that every real zero $\beta \in (0, 1)$ of the $L$-function of a primitive,
non-principal, real-valued Dirichlet character of modulus $q \ge 3$ satisfies
$(1 - \beta) q^{\varepsilon} \le c(\varepsilon)$. This literature milestone is
Siegel's theorem (1935), ineffective in the constant. The two source-file
Siegel statements of the mission (of logarithmic strength) go strictly beyond
it. The Lean statement is drafted for this mission (there is no source file
for it); the citation is given in the item's source field. Proved in the
literature; draft: the proof is a `sorry`.
-/

namespace SEF

theorem siegel_ineffective :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
        ∀ χ : DirichletCharacter ℂ q,
          χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
          ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
            (1 - β) * (q : ℝ) ^ ε ≤ c := by
  sorry

end SEF
