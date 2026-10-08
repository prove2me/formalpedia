-- Prove2me | Theorems.Thm_QLearning_Convergence_lemmaA_qIter_eq_arpQStar
-- name    : QLearning.Convergence.lemmaA_qIter_eq_arpQStar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:28.005516+00:00
-- url     : https://prove2.me/theorems/c2d6676a-d513-4c0e-b0dd-d9589fe69282
-- title:
--   Lemma A, p. 288 — Q_n(x, a) = Q*_ARP(⟨x, n⟩, a) for all a, x and n ≥ 0
-- statement:
--   Fix a discount $0<\gamma<1$, initial values $Q_0$, and any sequence of episodes $(x_n,a_n,y_n,r_n)_{n\ge1}$ with learning rates $0\le\alpha_n<1$. Let $Q_n$ be the Q-learning iterates (1) and $Q^*_{\mathrm{ARP}}$ the optimal action values of the action-replay process built from the same episodes. Then
--   $$Q_n(x,a)=Q^*_{\mathrm{ARP}}(\langle x,n\rangle,a)\qquad\text{for all }a,\ x\text{ and }n\ge0.$$
--
--   The lemma identifies the Q-learning iterates with exact optimal values of an auxiliary finite-horizon process; the convergence proof then compares that process with the real one.
--
--   **Formalization Note** $Q^*_{\mathrm{ARP}}$ is the supremum, over deterministic Markov policies of the ARP, of the policy's action value, which is defined by recursion on the level; it is not defined through the Q-learning rule. No hypothesis on the rewards or on condition (3) is needed: the identity holds for every deck.
-- source:
--   Watkins & Dayan, Technical Note: Q-Learning, Machine Learning 8 (1992), p. 288, Lemma A

import Mathlib
import Definitions.Def_QLearning_Convergence_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace QLearning.Convergence

theorem lemmaA_qIter_eq_arpQStar {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (Q0 : X → A → ℝ)
    (xs : ℕ → X) (as : ℕ → A) (ys : ℕ → X) (rs : ℕ → ℝ) (αs : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ αs n ∧ αs n < 1) :
    ∀ (n : ℕ) (x : X) (a : A),
      qIter γ Q0 xs as ys rs αs n x a = arpQStar γ Q0 xs as ys rs αs n x a := by sorry

end QLearning.Convergence
