-- Prove2me | Theorems.Thm_PetruzziDada_Additive_appendix_dR
-- name    : PetruzziDada.Additive.appendix_dR
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:14.627189+00:00
-- url     : https://prove2.me/theorems/a9402d89-6099-4b01-a043-8cd84481a355
-- title:
--   Appendix, proof of Theorem 1 (p. 192) — dE[Π(z, p(z))]/dz and dR(z)/dz
-- statement:
--   In the additive-demand price-setting newsvendor, let $p(z) = p^0 - \Theta(z)/2b$ (Lemma 1), let $F$ be the distribution function and $r(z) = f(z)/[1-F(z)]$ the hazard rate. Then:
--
--   1. the reduced objective $z \mapsto E[\Pi(z,p(z))]$ is differentiable at every real $z$, with
--   $$\frac{dE[\Pi(z,p(z))]}{dz} = -(c+h) + \Big[p^0 + s + h - \frac{\Theta(z)}{2b}\Big][1-F(z)];$$
--   2. writing $R(z) \equiv dE[\Pi(z,p(z))]/dz$, at every $z \in (A,B)$ at which the density $f$ is continuous and positive, $R$ is differentiable with
--   $$\frac{dR(z)}{dz} = -\frac{f(z)}{2b}\Big\{2b(p^0+s+h) - \Theta(z) - \frac{1-F(z)}{r(z)}\Big\}.$$
--
--   These are the first two displays of the paper's proof of Theorem 1 (Appendix, p. 192). The first combines eq. (5) with Lemma 1; the second is the starting point of the analysis of the zeros of $R$.
--
--   **Formalization Note** Continuity of $f$ at $z$ and $f(z) > 0$ are added for the second part: the first makes $F$ differentiable at $z$, and the second makes the paper's division by $r(z)$ meaningful.
-- source:
--   Petruzzi & Dada, Pricing and the Newsvendor Problem: A Review with Extensions, Oper. Res. 47(2) 1999, p. 192, Appendix, proof of Theorem 1, dE[Π(z, p(z))]/dz and dR(z)/dz

import Mathlib
import Definitions.Def_PetruzziDada_Additive_Model

open MeasureTheory

namespace PetruzziDada.Additive

/-- Appendix, proof of Theorem 1, p. 192: from the chain rule and Lemma 1,
`dE[Π(z, p(z))]/dz = -(c + h) + [p⁰ + s + h - Θ(z)/2b][1 - F(z)]` at every `z`; and, for
`z ∈ (A, B)` where `f` is continuous and positive,
`dR(z)/dz = -(f(z)/2b){2b(p⁰ + s + h) - Θ(z) - (1 - F(z))/r(z)}` with `R = dE[Π(z, p(z))]/dz`. -/
theorem appendix_dR (M : Model) :
    (∀ z : ℝ, HasDerivAt M.reducedProfit
        (-(M.c + M.h) + (M.p0 + M.s + M.h - M.Θ z / (2 * M.b)) * (1 - M.F z)) z) ∧
      ∀ z ∈ Set.Ioo M.A M.B, ContinuousAt M.f z → 0 < M.f z →
        HasDerivAt M.R
          (-(M.f z / (2 * M.b)) *
            (2 * M.b * (M.p0 + M.s + M.h) - M.Θ z - (1 - M.F z) / M.hazard z)) z := by sorry
end PetruzziDada.Additive
