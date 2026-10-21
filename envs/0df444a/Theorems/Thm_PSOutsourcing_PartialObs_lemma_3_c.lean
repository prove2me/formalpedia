-- Prove2me | Theorems.Thm_PSOutsourcing_PartialObs_lemma_3_c
-- name    : PSOutsourcing.PartialObs.lemma_3_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:58.159238+00:00
-- url     : https://prove2.me/theorems/3bd120eb-d1b0-4026-9611-d71c2123101f
-- title:
--   Lemma 3(c), p. 19 — ∂P(d^b_i − d_i ≥ X | s_i)/∂s_i ≥ 0
-- statement:
--   Let the model parameters satisfy the standing assumptions, let $s>0$ and $X\ge 0$. The function
--   $$
--   t\;\longmapsto\;\mathbb P\big(d^b-\xi_t d^b\ge X\big),\qquad \xi_t=\exp(tZ-t^2/2),\ Z\sim N(0,1),
--   $$
--   is differentiable at $t=s$ and its derivative there is nonnegative:
--   $$
--   \frac{\partial}{\partial s}\,\mathbb P\big(d^b-d\ge X\,\big|\,s\big)\ \ge\ 0 .
--   $$
--
--   This is Lemma 3(c): a larger information gap makes an upward drift of the belief by at least $X$ more likely. Proposition 4(b) rests on it.
--
--   **Formalization Note** The hypothesis $X\ge 0$ is added; the paper's proof uses $\ln(1-X/d^b)\le 0$, and for $X<0$ the derivative can be negative. The claim is stated with `HasDerivAt` (existence of the derivative and its sign), not with `deriv`, which is $0$ at points of non-differentiability. For $X\ge d^b$ the probability is identically $0$.
-- source:
--   Wang, Li, Ma & Zhang, Product service outsourcing: impact of environment uncertainty and partial observability, accepted manuscript (MSOM 2024, doi:10.1287/msom.2022.0222), p. 19 (PDF 19), Lemma 3(c); proof p. A-6 (PDF 38)

import Mathlib
import Definitions.Def_PSOutsourcing_PartialObs_Model

open MeasureTheory ProbabilityTheory

namespace PSOutsourcing.PartialObs

theorem lemma_3_c (P : Params) (hP : P.Standing) (s X : ℝ) (hs : 0 < s) (hX : 0 ≤ X) :
    ∃ D : ℝ, HasDerivAt (fun t => driftProb P t X) D s ∧ 0 ≤ D := by sorry

end PSOutsourcing.PartialObs
