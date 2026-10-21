-- Prove2me | Theorems.Thm_PSOutsourcing_PartialObs_lemma_3_a
-- name    : PSOutsourcing.PartialObs.lemma_3_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:56.304469+00:00
-- url     : https://prove2.me/theorems/06be3a27-049c-43a1-86a0-1b9ee23cbfee
-- title:
--   Lemma 3(a), p. 19 — the brand's belief is unbiased: E[d_i] = d^b_i
-- statement:
--   Let the model parameters satisfy the standing assumptions, with brand belief $d^b>0$, and let $s\in\mathbb R$. Let $\xi_s=\exp(sZ-s^2/2)$ with $Z\sim N(0,1)$ be the unobserved lognormal shock, so that the true service environment is $d=\xi_s d^b$. Then $\xi_s$ is integrable and
--   $$
--   \mathbb E[d]=\mathbb E[\xi_s\,d^b]=d^b .
--   $$
--
--   In the paper this is Lemma 3(a): the brand's belief is unbiased, $\mathbb E[d^b_i]=\mathbb E[d_i]$. It is the basic fact behind the expected-payment identity in the proof of Proposition 4(a).
--
--   **Formalization Note** The brand's belief $d^b$ is the conditioning information and is a fixed number here, so $\mathbb E[d^b_i]=d^b$ and the lemma reads $\mathbb E[d]=d^b$. Integrability of $\xi_s$ is stated so that the integral is not Lean's junk value $0$.
-- source:
--   Wang, Li, Ma & Zhang, Product service outsourcing: impact of environment uncertainty and partial observability, accepted manuscript (MSOM 2024, doi:10.1287/msom.2022.0222), p. 19 (PDF 19), Lemma 3(a); proof p. A-6 (PDF 38)

import Mathlib
import Definitions.Def_PSOutsourcing_PartialObs_Model

open MeasureTheory ProbabilityTheory

namespace PSOutsourcing.PartialObs

theorem lemma_3_a (P : Params) (hP : P.Standing) (s : ℝ) :
    Integrable (fun z => xi s z) (gaussianReal 0 1) ∧
      ∫ z, xi s z * P.db ∂(gaussianReal 0 1) = P.db := by sorry

end PSOutsourcing.PartialObs
