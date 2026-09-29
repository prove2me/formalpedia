-- Prove2me | Theorems.Thm_Schanuel_hermite_lindemann
-- name    : Schanuel.hermite_lindemann
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T17:31:11.422362+00:00
-- url     : https://prove2.me/theorems/f88819a5-647b-4cbb-854b-5c8bbfe23d70
-- title:
--   Hermite–Lindemann theorem
-- statement:
--   **Hermite–Lindemann theorem.** If $\alpha$ is a nonzero complex number that is algebraic over $\mathbb{Q}$, then $e^{\alpha}$ is transcendental over $\mathbb{Q}$: no nonzero polynomial with rational coefficients vanishes at $e^{\alpha}$.
--
--   Proved by Lindemann in 1882, extending Hermite's 1873 proof of the transcendence of $e$. Applied to $\alpha = i\pi$, together with $e^{i\pi} = -1$, it yields the transcendence of $\pi$.
-- source:
--   F. Lindemann, Über die Zahl π, Mathematische Annalen 20 (1882), 213–225; see also A. Baker, Transcendental Number Theory, CUP, 1975, Theorem 1.4

import Mathlib

namespace Schanuel
theorem hermite_lindemann (a : ℂ) (ha : IsAlgebraic ℚ a) (ha0 : a ≠ 0) :
    Transcendental ℚ (Complex.exp a) := by sorry
end Schanuel
