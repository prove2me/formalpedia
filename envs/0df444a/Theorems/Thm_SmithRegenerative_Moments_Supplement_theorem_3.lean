-- Prove2me | Theorems.Thm_SmithRegenerative_Moments_Supplement_theorem_3
-- name    : SmithRegenerative.Moments.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:45:24.627029+00:00
-- url     : https://prove2.me/theorems/2038bcff-ccc4-4591-afd7-2ab20d4dc619
-- title:
--   Theorem 3 — periodic equilibrium (corrected: span factor)
-- statement:
--   Let an equilibrium event have arbitrary positive maximal cycle span $w$, a certain first delay supported on the same lattice, and phase $0\le\xi<w$. If
--   $$\Sigma_A^\xi=\sum_{p=0}^\infty\phi_A(pw+\xi)P(t_1>pw+\xi)$$
--   converges, then
--   $$\lim_{p\to\infty}P_z(x_{pw+\xi}\in A)=\frac{w}{\mu_1}\Sigma_A^\xi.$$
--   For $\mu_1=\infty$ the limit is zero. No time-integrability or bounded-variation assumption is imposed on the sampled kernel. This is the lattice counterpart of the equilibrium renewal limit.
--
--   **Formalization Note** The printed factor $1/\mu_1$ is missing the span $w$. Deterministic cycles and delay equal to 2, and a constant state, give actual limit 1 and printed value 1/2. The lattice condition includes the degenerate delay at zero as the natural unshifted-lattice boundary convention.
--
--   Differences from the source:
--   - correction: The coefficient is 1/μ₁ in (3·5·2). → The coefficient is w/μ₁ for every positive span w.; reason: Time rescaling gives mean μ₁/w in lattice units; deterministic cycle length 2 disproves the printed coefficient. No case is excluded.
--   - reading: The delay period is the cycle period or an integer multiple. → The delay is supported on the unshifted cycle lattice, including the delay concentrated at zero.; reason: A nondegenerate lattice delay has the stated multiple span. The degenerate zero delay needs no greatest span and is included as a boundary convention.
--   - encoding: Real time and the paper’s distribution-function notation. → Probability measures with explicit mass at infinity and real-time limits; lattice sampling alone uses natural indices.; reason: Preserve defective laws, infinite means and the exact asymptotic domain without total-function defaults.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 16, Theorem 3

import Mathlib
import Definitions.Def_SmithRegenerative_Moments_Supplement_Equilibrium

namespace SmithRegenerative.Moments.Supplement

open MeasureTheory Filter Topology

/-- Smith (1955), Theorem 3, p. 16, (3·5·1)–(3·5·2), corrected span factor.
Formalization Note: arbitrary maximal span w>0, arbitrary real phase 0≤ξ<w, and
summability only of the sampled kernel. The finite delay is supported on the same unshifted lattice
(its own nondegenerate span is an integral multiple of w). Infinite cycle mean gives zero. Printed 1/μ is corrected to w/μ:
cycles and delay identically 2 with constant state give actual limit 1, not 1/2.
This is a change of units, with no excluded cases. -/
theorem theorem_3 {Ω X Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (E : Equilibrium Ω X Z) (z : Z) (A : Set X) (hA : A ∈ E.sets)
    (w ξ : ℝ) (hF : HasPeriod E.F w)
    (hK : OnLattice (E.K z) w)
    (hcertain : E.K z (Set.Iio ⊤) = 1)
    (hphase : 0 ≤ ξ ∧ ξ < w)
    (hsum : Summable (fun p : ℕ => kernel E A ((p : ℝ) * w + ξ))) :
    (extendedMean E.F = ⊤ →
      Tendsto (fun p : ℕ => (E.P z {ω | E.x ((p : ℝ) * w + ξ) ω ∈ A}).toReal)
        atTop (𝓝 0)) ∧
    (extendedMean E.F ≠ ⊤ →
      Tendsto (fun p : ℕ => (E.P z {ω | E.x ((p : ℝ) * w + ξ) ω ∈ A}).toReal)
        atTop (𝓝 (w / (extendedMean E.F).toReal *
          ∑' p : ℕ, kernel E A ((p : ℝ) * w + ξ)))) := by sorry

end SmithRegenerative.Moments.Supplement
