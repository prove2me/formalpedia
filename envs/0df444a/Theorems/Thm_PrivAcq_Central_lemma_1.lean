-- Prove2me | Theorems.Thm_PrivAcq_Central_lemma_1
-- name    : PrivAcq.Central.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:27.440985+00:00
-- url     : https://prove2.me/theorems/2feb4dc2-6f39-49d0-81ec-eee1a20cf304
-- title:
--   Lemma 1, p. 9 — the Laplace mechanism $f(x)+\mathrm{Laplace}(1/\varepsilon)$ is $(\varepsilon L_i(f))_i$-centrally private
-- statement:
--   Let $f : \mathcal X^n \to \mathbb R$ be a real-valued function of a dataset, and let $\varepsilon > 0$. For each user $i$ let $L_i$ be an upper bound on the sensitivity of $f$ in the $i$-th coordinate, i.e.
--   $$
--   |f(x) - f(x')| \le L_i \quad \text{whenever } x, x' \in \mathcal X^n \text{ differ only in the } i\text{-th coordinate}.
--   $$
--   Let $W \sim \mathrm{Laplace}(1/\varepsilon)$, the distribution with density $\frac{\varepsilon}{2} e^{-\varepsilon|z|}$. Then the algorithm $\mathcal A(x) = f(x) + W$ is $(\varepsilon L_i)_{i=1}^n$-centrally differentially private.
--
--   This is the per-user version of the classical Laplace mechanism of Dwork et al.: adding a single Laplace noise of scale $1/\varepsilon$ protects each user at a level proportional to that user's own influence on $f$.
--
--   **Formalization Note** The paper states the result with $L_i(f)$ equal to the supremum (1); here $L_i$ is any upper bound of the per-coordinate differences, which contains the paper's statement whenever the supremum is finite and avoids Lean's junk value of a real supremum of an unbounded set. The algorithm's output law is the Laplace law pushed forward by $u \mapsto f(x) + u$; `laplace s` is the published `PrivLearn.Generic.laplace`. The related posed theorem `PrivLearn.Parity.theorem_2_3` is the homogeneous, global-sensitivity version.
-- source:
--   Fallah, Makhdoumi, Malekian, Ozdaglar, arXiv:2201.03968v2, p. 9, Lemma 1 and (1)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivAcq_Central_CentralDP

namespace PrivAcq.Central

open MeasureTheory

theorem lemma_1 {X : Type*} {n : ℕ} (f : (Fin n → X) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (L : Fin n → ℝ)
    (hL : ∀ i : Fin n, ∀ x x' : Fin n → X, (∀ j : Fin n, j ≠ i → x j = x' j) →
      |f x - f x'| ≤ L i) :
    IsCentralDP (fun x => (PrivLearn.Generic.laplace (1 / ε)).map (fun u => f x + u))
      (fun i => ε * L i) := by sorry

end PrivAcq.Central
