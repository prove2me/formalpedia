-- Prove2me | Theorems.Thm_RandLatEnum_eq_2_7
-- name    : RandLatEnum.eq_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:30.938026+00:00
-- url     : https://prove2.me/theorems/a0e7b3b8-d5b8-4931-993b-728bbbe566d3
-- title:
--   Eq. (2.7) — $\Pr_{\mu_d}\{\lambda_1(L)<r_d/2\}\le\kappa_d(r_d/2)^d=2^{-d}/(2\zeta(d))$
-- statement:
--   Let $d\ge2$ and $L\sim\mu_d$. Then
--   $$
--   \Pr_{\mu_d}\bigl\{\lambda_1(L)<r_d/2\bigr\}\le\kappa_d\,(r_d/2)^d=\frac{2^{-d}}{2\zeta(d)} .
--   $$
--   The bound comes from Siegel's primitive-vector mean: the expected number of primitive pairs $\{\pm v\}$ in the ball of radius $r_d/2$ is its volume divided by $2\zeta(d)$, and a shortest vector is primitive. It gives $\lambda_1(L)\ge a\sqrt n$ with probability $1-e^{-\Omega(n)}$ in Proposition 3.1.
--
--   Differences from the source:
--   - encoding: the Haar probability measure µ_n on X_n → any SL_n(ℝ)-invariant Borel probability measure on X_n, taken as a hypothesis; reason: X_n has exactly one such measure (Siegel), so the instances are the same; Mathlib does not construct it
--   - encoding: the probability of an event → the measure of the set, i.e. its outer measure; reason: the paper assumes all choices measurable (p.14); for a measurable set the two agree, and the outer measure is the stronger reading
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.2, (2.7), p.15

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_RandLatEnum_X
import Definitions.Def_RandLatEnum_latticeOf
import Definitions.Def_RandLatEnum_IsHaarLatticeMeasure
import Definitions.Def_RandLatEnum_rGH
import Definitions.Def_RandLatEnum_kappa

namespace RandLatEnum

open MeasureTheory KannanLattice.Core

/-- **Eq. (2.7) (lower tail of `λ₁`)** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.2, (2.7), p.15). For `d ≥ 2`,
`P_{µ_d}{λ₁(L) < r_d/2} ≤ κ_d (r_d/2)^d = 2^{−d}/(2ζ(d))`.

**Formalization Note.** `µ_d` is any `SL_d(ℝ)`-invariant Borel probability measure on `X_d`; the
probability of the event is its (outer) measure. -/
theorem eq_2_7 (d : ℕ) (hd : 2 ≤ d) (μ : Measure (X d)) (hμ : IsHaarLatticeMeasure μ) :
    μ {x : X d | lambdaOne (latticeOf x : Set (EuclideanSpace ℝ (Fin d))) < rGH d / 2} ≤
        ENNReal.ofReal (kappa d * (rGH d / 2) ^ d) ∧
      kappa d * (rGH d / 2) ^ d = ((2 : ℝ) ^ d)⁻¹ / (2 * zetaReal d) := by sorry

end RandLatEnum
