-- Prove2me | Theorems.Thm_PetruzziDada_Additive_appendix_unimodal
-- name    : PetruzziDada.Additive.appendix_unimodal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:13.744984+00:00
-- url     : https://prove2.me/theorems/6b064213-5d67-40b3-a1a8-98a045700957
-- title:
--   Appendix, proof of Theorem 1 (p. 193) — under 2r² + r′ > 0, R is monotone or unimodal and has at most two roots
-- statement:
--   In the additive-demand price-setting newsvendor, let $R(z) = dE[\Pi(z,p(z))]/dz$ and suppose the hazard rate $r = f/(1-F)$ satisfies $2r(z)^2 + dr(z)/dz > 0$ for $A \le z < B$. Then $R$ is **monotone or unimodal** on $[A,B]$: there is $m \in [A,B]$ such that
--   $$R \text{ is strictly increasing on } [A,m] \quad\text{and strictly decreasing on } [m,B]$$
--   ($m = A$ or $m = B$ being the monotone cases). Consequently $R(z) = 0$ has at most two solutions in $[A,B]$.
--
--   This is the step of the paper's proof of Theorem 1 (p. 193) that turns the sign of $d^2R/dz^2$ at critical points into a global shape of $R$; it is the core of parts (b) and (c).
--
--   **Formalization Note** "Monotone or unimodal" is rendered as the existence of the turning point $m$ with strict monotonicity on both sides. The hazard condition is the one of the model file: on $[A,B)$, with the derivative of $r$ required to exist.
-- source:
--   Petruzzi & Dada, Pricing and the Newsvendor Problem: A Review with Extensions, Oper. Res. 47(2) 1999, p. 193, Appendix, proof of Theorem 1, R(z) either is monotone or unimodal

import Mathlib
import Definitions.Def_PetruzziDada_Additive_Model

open MeasureTheory

namespace PetruzziDada.Additive

/-- Appendix, proof of Theorem 1, p. 193: if `2r(z)² + dr(z)/dz > 0`, then `R(z)` either is
monotone or unimodal on `[A, B]` (strictly increasing up to some `m` and strictly decreasing
after it; `m = A` or `m = B` is the monotone case), so `R(z) = dE[Π(z, p(z))]/dz` has at most
two roots in `[A, B]`. -/
theorem appendix_unimodal (M : Model) (hr : M.HazardCondition) :
    (∃ m ∈ Set.Icc M.A M.B,
        StrictMonoOn M.R (Set.Icc M.A m) ∧ StrictAntiOn M.R (Set.Icc m M.B)) ∧
      {z ∈ Set.Icc M.A M.B | M.R z = 0}.encard ≤ 2 := by sorry
end PetruzziDada.Additive
