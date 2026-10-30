-- Prove2me | Theorems.Thm_PrivAcq_Central_proposition_1
-- name    : PrivAcq.Central.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:22.36201+00:00
-- url     : https://prove2.me/theorems/41162d6e-5fbc-4d5f-87c2-713eff34d408
-- title:
--   Proposition 1, p. 16 — IC and IR hold iff payments follow (19) with $d_i \ge 0$ and the interim privacy loss is weakly decreasing
-- statement:
--   Consider the data acquisition model under the standing assumptions, and an admissible mechanism of class (22) with privacy losses $\varepsilon$ and payments $t$. Write $h_i(c_i) = \mathbb E_{c_{-i}}[\mathrm{MSE}(c_i, c_{-i})]$, $\bar\varepsilon_i(c_i) = \mathbb E_{c_{-i}}[\varepsilon_i(c_i, c_{-i})]$ and $\bar t_i(c_i) = \mathbb E_{c_{-i}}[t_i(c_i, c_{-i})]$. The mechanism satisfies incentive compatibility (17) and individual rationality (18) if and only if, for every user $i$:
--
--   1. $\bar\varepsilon_i$ is weakly decreasing on $[a_i, b_i]$, and
--   2. there is a constant $d_i \ge 0$ such that for all $c_i \in [a_i, b_i]$
--   $$
--   \bar t_i(c_i) = h_i(c_i) - \mathrm{VAR} + c_i\,\bar\varepsilon_i(c_i) + \int_{c_i}^{b_i} \bar\varepsilon_i(z)\,dz + d_i. \qquad (19)
--   $$
--
--   This is the payment identity of the model, the analogue of Myerson's characterization of incentive compatible mechanisms, with the MSE appearing as an externality shared by all users.
--
--   **Formalization Note** The upper limit $\infty$ of the paper's integral becomes $b_i$, the upper end of the type support. Types and reports range over $[a_i,b_i]$. No differentiability of $\varepsilon$ or $t$ is assumed (the paper's Definition 3 does); admissibility gives measurability, bounded $\varepsilon$ and the integrability the interim expectations need.
-- source:
--   Fallah, Makhdoumi, Malekian, Ozdaglar, arXiv:2201.03968v2, p. 16, Proposition 1 and (19); proof pp. 42–43

import Mathlib
import Definitions.Def_PrivAcq_Central_Model

namespace PrivAcq.Central

open MeasureTheory

theorem proposition_1 {n : ℕ} (S : Setting n) (hS : S.Standing) (M : Mech n)
    (hM : Admissible S M) :
    IC S M ∧ IR S M ↔
      ∀ i : Fin n, AntitoneOn (interimEps S M i) (Set.Icc (S.a i) (S.b i)) ∧
        ∃ d : ℝ, 0 ≤ d ∧ ∀ ci ∈ Set.Icc (S.a i) (S.b i),
          interimPay S M i ci = interimMse S M i ci - S.var + ci * interimEps S M i ci +
            (∫ z in ci..S.b i, interimEps S M i z) + d := by sorry

end PrivAcq.Central
