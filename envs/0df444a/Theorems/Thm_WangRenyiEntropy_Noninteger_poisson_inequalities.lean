-- Prove2me | Theorems.Thm_WangRenyiEntropy_Noninteger_poisson_inequalities
-- name    : WangRenyiEntropy.Noninteger.poisson_inequalities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:39.798331+00:00
-- url     : https://prove2.me/theorems/9f7e7729-17c3-498c-b1d0-064cb7e3efe4
-- title:
--   Lemma 2.4 — five Poisson moment and tail inequalities
-- statement:
--   Let $X,Y$ be independent Poisson variables of the same rate $\lambda\ge0$, let $q\ge1$ be an integer, let $u>0$ and $0<v<1$. All displayed moments are finite, and all five inequalities hold:
--   $$\mathbb E X^q\le q^q\max\{\lambda,\lambda^q\},$$
--   $$\mathbb E|X-\lambda|^q\le(2q)^q\lambda^{q/2}\quad\text{if }\lambda\ge1,$$
--   $$\mathbb E(1+X+Y+\lambda)^q\le(4q)^q(1+\lambda)^q,$$
--   $$\Pr[X\ge(1+u)\lambda]\le\left(\frac{e^u}{(1+u)^{1+u}}\right)^\lambda,\qquad \Pr[X\le(1-v)\lambda]\le e^{-v^2\lambda/2}.$$
--   Only the central-moment clause needs $\lambda\ge1$. These inequalities control the exact estimator on the entire natural count range, including rate zero for the other clauses.
--
--   Differences from the source:
--   - encoding: independent variables with nonnegative Poisson rate → the canonical Poisson measure of a nonnegative real rate and its product law; reason: expectations and probabilities depend only on the joint distribution, so arbitrary independent realizations are covered
--   - encoding: Poisson moments in the five inequalities → their integrability is an explicit conclusion; reason: ensures every real integral denotes the finite expectation intended by the source
-- source:
--   Qisheng Wang, STOC 2027 submission #447 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/447.pdf, printed 7 / PDF 9, Lemma 2.4, Eqs. (2)–(6)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace WangRenyiEntropy.Noninteger

/-- Lemma 2.4, printed p.7 / PDF p.9, all five inequalities, including rate zero.
Integrability is a conclusion, not an additional assumption. -/
theorem poisson_inequalities (lam : ℝ≥0) (q : ℕ) (hq : 1 ≤ q)
    (u v : ℝ) (hu : 0 < u) (hv0 : 0 < v) (hv1 : v < 1) :
    let μ := poissonMeasure lam
    let ν := μ.prod μ
    Integrable (fun x : ℕ => (x : ℝ) ^ q) μ ∧
    Integrable (fun x : ℕ => |(x : ℝ) - (lam : ℝ)| ^ q) μ ∧
    Integrable (fun xy : ℕ × ℕ => (1 + (xy.1 : ℝ) + xy.2 + (lam : ℝ)) ^ q) ν ∧
    (∫ x : ℕ, (x : ℝ) ^ q ∂μ) ≤ (q : ℝ) ^ q * max (lam : ℝ) ((lam : ℝ) ^ q) ∧
    ((1 : ℝ) ≤ lam → (∫ x : ℕ, |(x : ℝ) - (lam : ℝ)| ^ q ∂μ) ≤
      (2 * q : ℝ) ^ q * Real.rpow lam ((q : ℝ) / 2)) ∧
    (∫ xy : ℕ × ℕ, (1 + (xy.1 : ℝ) + xy.2 + (lam : ℝ)) ^ q ∂ν) ≤
      (4 * q : ℝ) ^ q * (1 + (lam : ℝ)) ^ q ∧
    μ {x : ℕ | (1 + u) * (lam : ℝ) ≤ x} ≤
      ENNReal.ofReal (Real.rpow (Real.exp u / Real.rpow (1 + u) (1 + u)) lam) ∧
    μ {x : ℕ | (x : ℝ) ≤ (1 - v) * (lam : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(v ^ 2) * lam / 2)) := by sorry

end WangRenyiEntropy.Noninteger
