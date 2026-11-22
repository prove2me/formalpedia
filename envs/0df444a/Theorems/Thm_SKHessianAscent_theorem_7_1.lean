-- Prove2me | Theorems.Thm_SKHessianAscent_theorem_7_1
-- name    : SKHessianAscent.theorem_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:21:35.248205+00:00
-- url     : https://prove2.me/theorems/c94d546b-bd68-4168-b797-2e62f23f5d4e
-- title:
--   Theorem 7.1, desideratum (d6) — efficient sampling of $\mu_{\beta'A,y}$ on small Hamming wedges around $\mathrm{sign}(y)$
-- statement:
--   Fix $\beta>0$. There is $\varepsilon(\beta)>0$ and a randomized algorithm running in time polynomial in $n$ and $\log(1/\varepsilon)$ such that, with probability $1-o_n(1)$ over $A\sim\mathrm{GOE}(n)$, the following holds for all $0\le\beta'\le\beta$, all $y\in\mathbb R^n$ and all accuracies $0<\varepsilon<1/2$: on input $(\beta',\varepsilon,y,A)$ the algorithm outputs a sample whose law $\widehat\mu$ satisfies
--
--   $$
--   \mathrm{TV}\Big(\widehat\mu,\ \mu_{\beta'A,y}\big|_{B(\mathrm{sign}(y),\,\varepsilon(\beta)n)}\Big)\le\varepsilon,
--   $$
--
--   where $\mu_{\beta'A,y}(\sigma)\propto\exp(\tfrac12\langle\sigma,\beta'A\sigma\rangle+\langle y,\sigma\rangle)$ and $B(\sigma_0,k)=\{\sigma':d(\sigma_0,\sigma')\le k\}$ is the Hamming ball.
--
--   At large localization time the tilted measure concentrates on such a wedge, so this sampler finishes the algorithm; applied at all $\beta'\le\beta$ it also provides the partition-function estimates used in the rejection step.
--
--   **Formalization Note** The statement is the paper's desideratum (d6). Its Theorem 7.1 realizes it by [KSTZ26, Algorithm 2] with $\varepsilon(\beta)=1/(C\bar\beta^2\log(e\bar\beta))$, $\bar\beta=\max\{1,\beta\}$, and a prescribed number of annealing levels; here the algorithm is an existentially quantified admissible program of the `PolySampIso` real RAM and $\varepsilon(\beta)$ is an existentially quantified positive constant. The running time is at most $C((n+1)(1+\log(1/\varepsilon)))^k$ on every input and all random streams; the probability bound is a sequence $\eta_n\to0$ on the outer measure of the failure set; $\mathrm{sign}(0)=+1$.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, desideratum (d6), p. 6; Theorem 7.1, p. 42

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_PolySampIso_Machine
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Sampler

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem theorem_7_1 (β : ℝ) (hβ : 0 < β) :
    ∃ (ε₀ : ℝ) (P : PolySampIso.Program) (C k : ℕ) (η : ℕ → ℝ),
      0 < ε₀ ∧ PolySampIso.Admissible P ∧ Tendsto η atTop (𝓝 0) ∧
      (∀ (n : ℕ) (A : Fin n → Fin n → ℝ) (y : Fin n → ℝ) (β' ε : ℝ),
        0 ≤ β' → β' ≤ β → 0 < ε → ε < 1 / 2 →
          HaltsWithin P (initState n (wedgeMem β' ε y A))
            (C * (((n : ℝ) + 1) * (1 + Real.log (1 / ε))) ^ k)) ∧
      ∀ n : ℕ,
        RandMatDisc.goe n {A | ¬ ∀ (β' ε : ℝ) (y : Fin n → ℝ),
            0 ≤ β' → β' ≤ β → 0 < ε → ε < 1 / 2 →
              lawTV (outLaw P n (initState n (wedgeMem β' ε y A)))
                (wedgeLaw (tiltSK β' (Matrix.of A) y) (signSpin y) (ε₀ * n)) ≤ ε} ≤
          ENNReal.ofReal (η n) := by sorry

end SKHessianAscent
