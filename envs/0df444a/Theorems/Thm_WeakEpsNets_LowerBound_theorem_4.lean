-- Prove2me | Theorems.Thm_WeakEpsNets_LowerBound_theorem_4
-- name    : WeakEpsNets.LowerBound.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:07.374207+00:00
-- url     : https://prove2.me/theorems/31d73217-3b49-4811-8cdf-cca08a791c40
-- title:
--   Theorem 4 — full asymptotic lower bound in dimension D_s
-- statement:
--   For every integer $s\ge1$, set $D_s=(s^2+5s)/2$. There exist positive constants $r_s,c_s$ such that, for every real $r\ge r_s$, there is a finite nonempty set $P\subset\mathbb R^{D_s}$ for which every finite weak $1/r$-net $X$ with respect to all convex sets satisfies
--   $$|X|\ge c_s r^{(s+2)/2}.$$
--   The constants may depend on $s$, while the assertion covers every sufficiently large real $r$. This is the asymptotic milestone connecting the explicit construction to the dimension-dependent goal.
--
--   Differences from the source:
--   - reading: finite point sets whose weak nets require $\Omega(r^{(s+2)/2})$ points → positive $r_s,c_s$ chosen before every real $r\ge r_s$, followed by a finite nonempty witness set and the universal net lower bound; reason: this is the full eventual lower-bound reading, consistent with the text saying Theorem 4 is equivalent to Theorem 1; it is not restricted to construction parameters
--   - encoding: $\mathbb R^{D_s}$ and the power $r^{(s+2)/2}$ → real functions on $\mathrm{Fin}(D_s)$ and Real.rpow with real exponent $(s+2)/2$; reason: these are the same finite-dimensional vector space and real power; natural division in $D_s$ is exact
-- source:
--   Bhore, Browne, Zheng, Strong Lower Bounds for Weak Epsilon-Nets, STOC 2027 submission #301 (October 2026), Theorem 4, p. 10, lines 299–301; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/301.pdf

import Mathlib
import Definitions.Def_WeakEpsNets_LowerBound_Nets
import Definitions.Def_WeakEpsNets_LowerBound_Parameters

namespace WeakEpsNets.LowerBound

/-- Theorem 4, source p. 10: Ω means every sufficiently large real r. -/
theorem theorem_4 (s : ℕ) (hs : 1 ≤ s) :
    ∃ rₛ : ℝ, 0 < rₛ ∧ ∃ cₛ : ℝ, 0 < cₛ ∧
      ∀ r : ℝ, rₛ ≤ r →
        ∃ P : Finset (Fin (liftDimension s) → ℝ), P.Nonempty ∧
          ∀ X : Finset (Fin (liftDimension s) → ℝ), IsWeakNet P r X →
            cₛ * Real.rpow r (((s : ℝ) + 2) / 2) ≤ (X.card : ℝ) := by sorry

end WeakEpsNets.LowerBound
