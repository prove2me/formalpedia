-- Prove2me | Theorems.Thm_PSOutsourcing_PartialObs_lemma_3_b
-- name    : PSOutsourcing.PartialObs.lemma_3_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:04.221988+00:00
-- url     : https://prove2.me/theorems/5aaf817a-b514-4a0c-bc38-cf8bcda9196b
-- title:
--   Lemma 3(b), eq. (10), p. 19 — P(d^b_i − d_i ≥ X | s_i) = ½(1 + erf((ln(1 − X/d^b_i) + s_i²/2)/(√2 s_i)))
-- statement:
--   Let the model parameters satisfy the standing assumptions, with belief $d^b>0$, let $s>0$, and let $X<d^b$. With $d=\xi_s d^b$ the true environment, $\xi_s=\exp(sZ-s^2/2)$, $Z\sim N(0,1)$,
--   $$
--   \mathbb P\big(d^b-d\ge X\big)=\frac12\left(1+\operatorname{erf}\!\left(\frac{\ln\big(1-X/d^b\big)^{+}+s^2/2}{\sqrt2\,s}\right)\right),
--   $$
--   where $\operatorname{erf}(x)=\frac{2}{\sqrt\pi}\int_0^x e^{-t^2}dt$ is the error function.
--
--   This is equation (10) of Lemma 3(b): the probability that the brand's belief exceeds the true environment by at least $X$.
--
--   **Formalization Note** The hypothesis $X<d^b$ is added: for $X\ge d^b$ the paper's formula uses $\ln 0=-\infty$ (giving probability $0$), whereas Lean's `Real.log 0 = 0`. Under $X<d^b$ the positive part $(\cdot)^+$, kept as `max (1 - X/d^b) 0`, is inactive. The hypothesis $s>0$ is needed for the division by $s$.
-- source:
--   Wang, Li, Ma & Zhang, Product service outsourcing: impact of environment uncertainty and partial observability, accepted manuscript (MSOM 2024, doi:10.1287/msom.2022.0222), p. 19 (PDF 19), Lemma 3(b), eq. (10); proof p. A-6 (PDF 38)

import Mathlib
import Definitions.Def_PSOutsourcing_PartialObs_Model

open MeasureTheory ProbabilityTheory

namespace PSOutsourcing.PartialObs

theorem lemma_3_b (P : Params) (hP : P.Standing) (s X : ℝ) (hs : 0 < s) (hX : X < P.db) :
    driftProb P s X =
      1 / 2 * (1 + erf ((Real.log (max (1 - X / P.db) 0) + s ^ 2 / 2) / (Real.sqrt 2 * s))) := by sorry

end PSOutsourcing.PartialObs
