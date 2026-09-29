-- Prove2me | Theorems.Thm_SatiaLave_Bayes_no_learning_reduces_to_mdp
-- name    : SatiaLave.Bayes.no_learning_reduces_to_mdp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:43:32.177926+00:00
-- url     : https://prove2.me/theorems/c81eb972-3a99-47b8-b2e0-2a700a29cd31
-- title:
--   § Bayesian Formulation — without learning the problem reduces to a Markovian decision process
-- statement:
--   In the Bayesian formulation of Satia and Lave the decision maker holds a prior $g$ on the unknown transition matrix $P$ and updates it by the Bayes transformation $T^m_{lj}$ of Eq. (8) after each transition. Let $f(i,g)$ be any solution of the recursive equations (10).
--
--   Let $P$ be a transition-probability matrix (every row $p_i^k$ a probability vector) and let $\delta_P$ be the point mass at $P$, a prior under which there is nothing to learn. Then
--
--   1. every Bayes transformation leaves $\delta_P$ unchanged: $T^m_{lj}\delta_P = \delta_P$ for all $l$, $m$, $j$;
--   2. the values $V_i = f(i, \delta_P)$ solve the optimality equations of the Markovian decision process with known transition matrix $P$:
--   $$
--   V_i = \max_{k \in K_i} \sum_j p^k_{ij}\big(r^k_{ij} + \beta V_j\big) \qquad \text{for every state } i.
--   $$
--
--   This is the paper's remark "If there is no learning involved, the problem reduces to a Markovian decision process", and it is the fact the proof of Proposition 9 uses at the point masses $a_x$.
--
--   **Formalization Note** "No learning" is read as a point-mass prior, which is exactly a prior fixed by every Bayes transformation. The paper's remark does not name an equation; the reduction is stated as the known-$P$ optimality equations (Howard's model).
-- source:
--   Satia and Lave, Markovian Decision Processes with Uncertain Transition Probabilities, Operations Research 21(3), 1973, p. 733, § Bayesian Formulation (last sentence before Proposition 6)

import Mathlib
import Definitions.Def_SatiaLave_Bayes_Model

open MeasureTheory

namespace SatiaLave.Bayes

/-- § Bayesian Formulation, p. 733: without learning (a point-mass prior at a transition
matrix `P`, which every Bayes transformation leaves unchanged) the recursion (10) reduces to the
optimality equations of the Markovian decision process with the known matrix `P`. -/
theorem no_learning_reduces_to_mdp {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D)
    (f : S → Measure (Mat S D) → ℝ) (hf : SolvesEq10 M f)
    (P : Mat S D) (hP : IsStoch P) :
    (∀ (l : S) (m : D l) (j : S), bayes (Measure.dirac P) l m j = Measure.dirac P) ∧
    SolvesKnown M P (fun i => f i (Measure.dirac P)) := by sorry

end SatiaLave.Bayes
