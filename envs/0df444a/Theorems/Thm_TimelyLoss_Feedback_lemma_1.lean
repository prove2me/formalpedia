-- Prove2me | Theorems.Thm_TimelyLoss_Feedback_lemma_1
-- name    : TimelyLoss.Feedback.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:45.684436+00:00
-- url     : https://prove2.me/theorems/45a9837d-acef-4505-9fbf-cf4631aef0a1
-- title:
--   Lemma 1, p. 13 (PDF 14) — the firm invests iff µ > µ̄, divests iff µ < µ̲, else keeps the status quo
-- statement:
--   Let $\mu\in[0,1]$ be the firm's posterior probability of state $H$, and for an investment choice $d\in\{-1,0,1\}$ let
--   $$E_\mu[v(d)]=\mu\,v(H,d)+(1-\mu)\,v(L,d).$$
--   Let $\bar\mu=\tfrac12+\tfrac{c}{2x}$ and $\underline\mu=\tfrac12-\tfrac{c}{2x}$, and let $d^*(\mu)$ be the rule "increase if $\mu>\bar\mu$, decrease if $\mu<\underline\mu$, keep otherwise". Throughout, the standing assumptions of §2.1 hold: $0<c<x$, $R_L+x<R_H-x$, $0<\beta<1$, $\lambda>2c/(x+c)$, together with $\lambda<1$ and $0<f<1$. Then:
--
--   1. $d^*(\mu)$ maximizes $E_\mu[v(d)]$ over $d\in\{-1,0,1\}$;
--   2. if $\mu>\bar\mu$, increasing investment is strictly better than either alternative;
--   3. if $\mu<\underline\mu$, decreasing investment is strictly better than either alternative.
--
--   $$d^*(\mu)\in\arg\max_{d\in\{-1,0,1\}}E_\mu[v(d)].$$
--
--   This lemma justifies the firm's decision rule that the model uses whenever the firm learns from the order flow.
--
--   **Formalization Note** At $\mu=\bar\mu$ or $\mu=\underline\mu$ the firm is indifferent and the rule keeps the status quo, the paper's tie-break.
-- source:
--   Chen, Huang, Jiang, Zhang & Zhang, The Role of Asymmetric Disclosure When Price Efficiency Affects Real Efficiency, working paper (PDF of 2018-08; published as "Asymmetric Reporting Timeliness and Informational Feedback", Management Science 2021), p. 13 (PDF 14), Lemma 1

import Mathlib
import Definitions.Def_TimelyLoss_Feedback_Model

namespace TimelyLoss.Feedback

theorem lemma_1 (P : Params) (hP : P.Standing) (μ : ℝ)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    (∀ d : Dec, expectedValue P μ d ≤ expectedValue P μ (firmRule P μ)) ∧
    (muBar P < μ → ∀ d : Dec, d ≠ .up →
      expectedValue P μ d < expectedValue P μ .up) ∧
    (μ < muLow P → ∀ d : Dec, d ≠ .down →
      expectedValue P μ d < expectedValue P μ .down) := by sorry

end TimelyLoss.Feedback
