-- Prove2me | Theorems.Thm_PrivAcq_Central_proposition_2
-- name    : PrivAcq.Central.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:30.319005+00:00
-- url     : https://prove2.me/theorems/9aae55a3-b3b9-4541-bf74-7450f231010c
-- title:
--   Proposition 2, p. 17 — the platform's problem reduces to minimizing $\mathbb E_c[(n+1)\mathrm{MSE} + \sum_i \varepsilon_i\psi_i(c_i)] - n\,\mathrm{VAR}$ under (21)
-- statement:
--   Under the standing assumptions of the model:
--
--   1. For every admissible mechanism that is incentive compatible (17) and individually rational (18),
--   $$
--   \mathbb E_c\Big[\mathrm{MSE}(c) + \sum_{i=1}^n t_i(c)\Big] \;\ge\; \mathbb E_c\Big[(n+1)\,\mathrm{MSE}(c) + \sum_{i=1}^n \varepsilon_i(c)\,\psi_i(c_i)\Big] - n\,\mathrm{VAR}. \qquad (20)
--   $$
--   2. Conversely, for every admissible allocation $(w, \eta, \varepsilon)$ whose interim privacy losses $\bar\varepsilon_i(z) = \mathbb E_{c_{-i}}[\varepsilon_i(z, c_{-i})]$ are weakly decreasing in $z$ (constraint (21)), equipping it with the payments (19) with $d_i = 0$ gives an admissible, incentive compatible and individually rational mechanism whose objective equals the right-hand side of (20).
--
--   Hence the optimal privacy losses are the solution of minimizing the right-hand side of (20) subject to (21): the analogue of Myerson's reduction of mechanism design to virtual welfare maximization.
--
--   **Formalization Note** The paper's "the optimal privacy loss … is the solution of (20)–(21)" is stated as the two inequalities/equalities that make the two problems equivalent. Payments (19) are used in ex post form, $t_i(c) = \mathrm{MSE}(c) - \mathrm{VAR} + c_i\varepsilon_i(c) + \int_{c_i}^{b_i}\varepsilon_i(z, c_{-i})\,dz$.
-- source:
--   Fallah, Makhdoumi, Malekian, Ozdaglar, arXiv:2201.03968v2, p. 17, Proposition 2, (20), (21); proof p. 44, (A35)

import Mathlib
import Definitions.Def_PrivAcq_Central_Model

namespace PrivAcq.Central

open MeasureTheory

theorem proposition_2 {n : ℕ} (S : Setting n) (hS : S.Standing) :
    (∀ M : Mech n, Admissible S M → IC S M → IR S M →
      (∫ c, (((n : ℝ) + 1) * mse S M c + ∑ i, M.ε c i * S.ψ i (c i)) ∂S.typeLaw)
          - (n : ℝ) * S.var ≤ objective S M) ∧
    (∀ M : Mech n, AdmissibleAlloc S M →
      (∀ i : Fin n, AntitoneOn (interimEps S M i) (Set.Icc (S.a i) (S.b i))) →
      Admissible S (withPayments S M) ∧ IC S (withPayments S M) ∧ IR S (withPayments S M) ∧
        objective S (withPayments S M) =
          (∫ c, (((n : ℝ) + 1) * mse S M c + ∑ i, M.ε c i * S.ψ i (c i)) ∂S.typeLaw)
            - (n : ℝ) * S.var) := by sorry

end PrivAcq.Central
