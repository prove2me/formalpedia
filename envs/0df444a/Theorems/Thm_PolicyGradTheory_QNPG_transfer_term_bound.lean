-- Prove2me | Theorems.Thm_PolicyGradTheory_QNPG_transfer_term_bound
-- name    : PolicyGradTheory.QNPG.transfer_term_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:34:29.03773+00:00
-- url     : https://prove2.me/theorems/8753dfce-1b8a-408b-b078-b56461479c79
-- title:
--   (25), p. 39 — comparator transfer term bounded by Q-prediction loss
-- statement:
--   Fix a comparator policy π⋆, a starting distribution ρ, log-linear features φ, a parameter θ, and any weight vector w. Under $d^\star=d^{\pi^\star}_\rho\times\mathrm{Unif}_A$, the comparator-weighted discrepancy between advantage and the log-policy score obeys
--
--   $$
--   \mathbb E_{s\sim d^{\pi^\star}_\rho,a\sim\pi^\star}
--     [A^{\pi_\theta}(s,a)-w\cdot\nabla_\theta\log\pi_\theta(a\mid s)]
--     \le 2\sqrt{|A|\,L(w;\theta,d^\star)}.
--   $$
--
--   This controls the transfer component of the regret error by a prediction loss under the comparator's states.
--
--   **Formalization Note** The paper displays this inequality for its exact minimizer $w_\star^{(t)}$; the displayed derivation uses no minimizing property, so this statement allows any w.
-- source:
--   arXiv:1908.00261v5, (25), proof of Theorem 6.1, p. 39

import Mathlib
import Definitions.Def_PolicyGradTheory_QNPG_Setting

namespace PolicyGradTheory.QNPG

open FoundationsML.ReinforcementLearning

/-- Inequality (25), proof of Theorem 6.1, p. 39. The displayed proof
uses no minimizing property of its weight vector. -/
theorem transfer_term_bound {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A] {d : ℕ}
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar)
    (φ : S → A → EuclideanSpace ℝ (Fin d))
    (θ w : EuclideanSpace ℝ (Fin d)) :
    (∑ s : S, PolicyGradTheory.ProjGA.visitation πstar P γ ρ s *
      ∑ a : A, πstar s a *
        (PolicyGradTheory.ProjGA.advantage (logLinearPolicy φ θ) P r γ s a -
          inner ℝ w (gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ))) ≤
      2 * Real.sqrt ((Fintype.card A : ℝ) *
        qLoss P r γ φ w θ (dstar P γ ρ πstar)) := by sorry

end PolicyGradTheory.QNPG
