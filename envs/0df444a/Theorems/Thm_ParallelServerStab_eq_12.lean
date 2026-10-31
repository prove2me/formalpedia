-- Prove2me | Theorems.Thm_ParallelServerStab_eq_12
-- name    : ParallelServerStab.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:56.418262+00:00
-- url     : https://prove2.me/theorems/a01cdfcf-7ea0-4f1e-9a6b-6a273f801061
-- title:
--   Eq. (12) — $V_{cr}(1)$ is the positive root, and $(s\rho)^2/(1+s\rho)>s-1$ iff $\rho>V_{cr}(1)$
-- statement:
--   Let $s\ge2$. Then
--
--   1. $V_{cr}(1)<1$;
--   2. $V_{cr}(1)$ is the only positive root of the polynomial $x\mapsto s^2x^2-(s-1)sx-(s-1)$;
--   3. for every $\rho>0$,
--
--   $$
--   \frac{(s\rho)^2}{1+s\rho}>s-1\iff \rho>V_{cr}(1).
--   $$
--
--   For J2SQ$^{NI}$ the front server is a loss system, the overflow to the back servers has rate $\lambda^2/(\lambda+\mu)$, and (12) says this exceeds the back capacity $(s-1)\mu$ exactly when $\rho>V_{cr}(1)$.
--
--   Differences from the source:
--   - reading: $s \ge 1$ servers in (9), $s$ servers in §3 → $s \ge 2$; reason: the model has $s \ge 2$ servers (§1, p. 1), $p_{p,2}=(1-p,p,0,\dots,0)$ needs two coordinates, and (9) divides by $p(s-1)$
-- source:
--   Moyal–Perry, Stability of Parallel Server Systems, arXiv:1904.10331v1, proof of Proposition 2, eq. (12) and the sentence before it, p.12

import Mathlib
import Definitions.Def_ParallelServerStab_Vcr

namespace ParallelServerStab

/-- The `p = 1` algebra and (12) (Moyal–Perry, Stability of Parallel Server Systems,
arXiv:1904.10331v1, proof of Proposition 2, eq. (12), p. 12). For `s ≥ 2`:
1. `V_cr(1) < 1`;
2. `V_cr(1)` is the only positive root of `x ↦ s²x² − (s − 1)sx − (s − 1)`;
3. for every `ρ > 0`, `(sρ)²/(1 + sρ) > s − 1` if and only if `ρ > V_cr(1)`. -/
theorem eq_12 (s : ℕ) (hs : 2 ≤ s) :
    Vcr s 1 < 1 ∧
    (∀ x : ℝ, 0 < x →
      ((s : ℝ) ^ 2 * x ^ 2 - ((s : ℝ) - 1) * s * x - ((s : ℝ) - 1) = 0 ↔ x = Vcr s 1)) ∧
    ∀ ρ : ℝ, 0 < ρ → (((s : ℝ) - 1) < (s * ρ) ^ 2 / (1 + s * ρ) ↔ Vcr s 1 < ρ) := by sorry

end ParallelServerStab
