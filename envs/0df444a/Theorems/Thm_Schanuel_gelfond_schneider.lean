-- Prove2me | Theorems.Thm_Schanuel_gelfond_schneider
-- name    : Schanuel.gelfond_schneider
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T17:33:14.472082+00:00
-- url     : https://prove2.me/theorems/2e4b9062-99bc-4797-b90c-279b63f084aa
-- title:
--   Gelfond–Schneider theorem (logarithmic form)
-- statement:
--   **Gelfond–Schneider theorem, logarithmic form.** Let $\lambda$ be a nonzero complex number whose exponential $e^{\lambda}$ is algebraic (that is, $\lambda$ is a nonzero logarithm of an algebraic number), and let $\beta$ be an algebraic number that is not rational. Then $e^{\beta \lambda}$ is transcendental.
--
--   Writing $\alpha = e^{\lambda}$ and $\alpha^{\beta} = e^{\beta\lambda}$ for the corresponding branch, this is the classical statement that $\alpha^{\beta}$ is transcendental for algebraic $\alpha \notin \{0, 1\}$ and algebraic irrational $\beta$ — Hilbert's seventh problem, solved independently by Gelfond and by Schneider in 1934. It yields the transcendence of $2^{\sqrt 2}$ and of $e^{\pi} = (-1)^{-i}$.
-- source:
--   A. O. Gelfond, Sur le septième problème de Hilbert, Izv. Akad. Nauk SSSR (1934), 623–634; Th. Schneider, Transzendenzuntersuchungen periodischer Funktionen, J. Reine Angew. Math. 172 (1934), 65–69; see A. Baker, Transcendental Number Theory, CUP, 1975, Theorem 2.1

import Mathlib

namespace Schanuel
theorem gelfond_schneider (b l : ℂ) (hb : IsAlgebraic ℚ b) (hbq : ∀ q : ℚ, b ≠ (q : ℂ))
    (hl : IsAlgebraic ℚ (Complex.exp l)) (hl0 : l ≠ 0) :
    Transcendental ℚ (Complex.exp (b * l)) := by sorry
end Schanuel
