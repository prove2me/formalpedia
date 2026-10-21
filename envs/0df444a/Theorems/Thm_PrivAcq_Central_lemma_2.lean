-- Prove2me | Theorems.Thm_PrivAcq_Central_lemma_2
-- name    : PrivAcq.Central.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:32.262384+00:00
-- url     : https://prove2.me/theorems/f2edf54b-f0e9-4794-9aac-1166a2078947
-- title:
--   Lemma 2, p. 10 — the linear estimator (3) is $(w_i\eta)_{i=1}^n$-centrally differentially private
-- statement:
--   Let $\theta \in \mathbb R$ be the unknown mean, so that every data point lies in $\mathcal X = [\theta - \tfrac12, \theta + \tfrac12]$ (the data are $X_i = \theta + Z_i$ with $|Z_i| \le \tfrac12$). Let $\eta > 0$ and let $w_1,\dots,w_n \ge 0$ be weights with $\sum_{i=1}^n w_i = 1$. The linear estimator with Laplace mechanism (3),
--   $$
--   \hat\theta(x_1,\dots,x_n) = \sum_{i=1}^n w_i x_i + \mathrm{Laplace}(1/\eta),
--   $$
--   is $(w_i\eta)_{i=1}^n$-centrally differentially private on datasets $x \in \mathcal X^n$.
--
--   This is what links the estimator weights to the privacy levels: user $i$'s privacy loss is $w_i \eta$, the constraint $\eta w_i \le \varepsilon_i$ in the mechanism class (22).
--
--   **Formalization Note** The weights are assumed nonnegative (for a negative $w_i$ the privacy level would be $|w_i|\eta$); the data space $[\theta - \tfrac12, \theta + \tfrac12]$ encodes $|Z_i| \le \tfrac12$ from p. 7.
-- source:
--   Fallah, Makhdoumi, Malekian, Ozdaglar, arXiv:2201.03968v2, p. 10, Lemma 2 and (3); proof on p. 37

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivAcq_Central_CentralDP

namespace PrivAcq.Central

open MeasureTheory

theorem lemma_2 {n : ℕ} (θ η : ℝ) (hη : 0 < η) (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    IsCentralDP (X := Set.Icc (θ - 1 / 2) (θ + 1 / 2))
      (fun x => (PrivLearn.Generic.laplace (1 / η)).map (fun u => ∑ i, w i * (x i : ℝ) + u))
      (fun i => w i * η) := by sorry

end PrivAcq.Central
