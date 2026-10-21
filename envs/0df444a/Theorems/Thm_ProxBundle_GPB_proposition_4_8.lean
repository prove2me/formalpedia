-- Prove2me | Theorems.Thm_ProxBundle_GPB_proposition_4_8
-- name    : ProxBundle.GPB.proposition_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:26.553885+00:00
-- url     : https://prove2.me/theorems/4c6cabcd-af65-4e9b-8e01-8e41f41f1b47
-- title:
--   Proposition 4.8, p. 17 — finite cycle bound
-- statement:
--   Starting from a serious GPB index $j_0$ before the first $\bar\varepsilon$-solution, let $j_1$ be the next serious index. Such an index exists, all indices strictly between $j_0$ and $j_1$ are null, and with $\bar t$ from (58),
--   $$
--   j_1-j_0\le\left\lceil\frac{\max\{\log(4\bar t/\bar\varepsilon),0\}}{1-\tau}\right\rceil+1.
--   $$
--   In particular, if $\tau$ is given by (38) for a pair $(M_f,L_f)$ with $M_f^2+\bar\varepsilon L_f>0$, then, with $\lambda_\mu=\lambda/(1+\lambda\mu)$,
--   $$
--   j_1-j_0\le\left\lceil\left(1+\frac{8\lambda_\mu(M_f^2+\bar\varepsilon L_f)}{\bar\varepsilon}\right)\max\{\log(4\bar t/\bar\varepsilon),0\}\right\rceil+1,
--   $$
--   which is (60).
--   The statement bounds the cardinality of a cycle of consecutive null steps followed by a serious step.
--
--   **Formalization Note** The ceiling and nonnegative logarithm correct the omitted integer rounding and small-$\bar t$ case in printed (59) and (60). Clause (60) assumes $M_f^2+\bar\varepsilon L_f>0$, without which (38) does not give $\tau\in(0,1)$.
-- source:
--   Liang & Monteiro, arXiv:2110.01084v3, p. 17, Proposition 4.8, (59)–(60)

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model

namespace ProxBundle.GPB

/-- Proposition 4.8, p. 17: a finite cycle with the rounding correction to (59),
and its specialization (60) when τ is given by (38). -/
theorem proposition_4_8 {n : ℕ} (P : Instance n) (μ Mbar Lbar lam ε τ : ℝ)
    (x0 x0s : E n) (R : Run n)
    (hμ : 0 ≤ μ) (hM : 0 ≤ Mbar) (hL : 0 ≤ Lbar)
    (hA1 : P.A1 μ) (hA3 : P.A3 Mbar Lbar)
    (hlam : 0 < lam) (hε : 0 < ε)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (h29 : Cond29 μ lam ε τ Mbar Lbar)
    (hx0 : x0 ∈ P.D) (hopt : P.IsNearestOpt x0 x0s)
    (hrun : IsRun P μ lam ε τ x0 R)
    (j0 : ℕ) (hserious : R.t P lam j0 ≤ ε / 2)
    (hbefore : j0 = 0 ∨ ε < P.φ (R.y j0) - P.φ x0s) :
    ∃ j1 : ℕ, j0 < j1 ∧ R.t P lam j1 ≤ ε / 2 ∧
      (∀ i : ℕ, j0 < i → i < j1 → ε / 2 < R.t P lam i) ∧
      (((j1 - j0 : ℕ) : ℝ) ≤
        (⌈max (Real.log (4 * tbar Mbar Lbar lam ‖x0 - x0s‖ / ε)) 0 /
          (1 - τ)⌉ : ℝ) + 1) ∧
      (∀ Mf Lf : ℝ, 0 < Mf ^ 2 + ε * Lf → τ = tau38 μ lam ε Mf Lf →
        ((j1 - j0 : ℕ) : ℝ) ≤
          (⌈(1 + 8 * lamMu μ lam * (Mf ^ 2 + ε * Lf) / ε) *
            max (Real.log (4 * tbar Mbar Lbar lam ‖x0 - x0s‖ / ε)) 0⌉ : ℝ) + 1) := by sorry

end ProxBundle.GPB
