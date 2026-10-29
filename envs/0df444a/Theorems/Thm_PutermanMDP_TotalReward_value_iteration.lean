-- Prove2me | Theorems.Thm_PutermanMDP_TotalReward_value_iteration
-- name    : PutermanMDP.TotalReward.value_iteration
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:32:15.161565+00:00
-- url     : https://prove2.me/theorems/a291e375-601b-4b03-a1eb-89daca45bc0d
-- title:
--   Theorem 7.2.12 — Monotone convergence of total-reward value iteration
-- statement:
--   Let a positive bounded model have a nonempty finite or countably infinite state space and nonempty finite or countably infinite action sets. Every admissible history-dependent randomized policy must have finite expected accumulated positive reward at each initial state, and every state must offer an action of nonnegative immediate reward. Starting with the zero function, define
--   $$
--   v^0=0,\qquad v^{n+1}=\mathcal Lv^n.
--   $$
--   Then every iterate is pointwise finite and nonnegative, and for every state $s$,
--   $$
--   v^n(s)\uparrow v^*(s)<\infty,
--   $$
--   where $v^*$ is the supremum of expected total rewards over all admissible history-dependent randomized policies. Convergence is pointwise and monotone; no rate or uniform convergence is asserted.
--
--   The result supplies a value-iteration characterization of the total-reward optimum without discounting.
--
--   **Formalization Note** Lean uses extended values to define the iteration without replacing divergent sums by zero, and concludes that the iterates and limiting optimum are finite. Convergence in the extended-real order topology to the displayed finite real value is equivalent to ordinary real convergence. Finiteness is also explicit in the source proof on p. 294.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 294, proof continued p. 295 (PDF 310–311), Theorem 7.2.12

import Mathlib
import Definitions.Def_PutermanMDP_TotalReward_Bellman

/-
Dependency source for blind auditing. The following is a verbatim snapshot
of the two imported definition modules; these are comments, not redeclarations.

import Mathlib
open scoped ENNReal

namespace PutermanMDP.TotalReward

/-- The time-homogeneous discrete model of §§2.1 and 7.1. Actions depend on the state.
Countability and nonemptiness are imposed by each theorem, not finiteness. -/
structure Model (S : Type*) (A : S → Type*) where
  reward : (s : S) → A s → ℝ
  transition : (s : S) → A s → PMF S

/-- Observable history: the preceding state/action pairs in chronological order,
followed by the current state. Its list length is the zero-based decision epoch. -/
abbrev History (S : Type*) (A : S → Type*) := List (Sigma A) × S

/-- All admissible history-dependent randomized policies, including decisions on
histories of probability zero. The dependent action type enforces admissibility. -/
abbrev HRPolicy (S : Type*) (A : S → Type*) := (h : History S A) → PMF (A h.2)

/-- Time-dependent randomized Markov policies. -/
abbrev MRPolicy (S : Type*) (A : S → Type*) := ℕ → (s : S) → PMF (A s)

def markovPolicy {S : Type*} {A : S → Type*} (π : MRPolicy S A) : HRPolicy S A :=
  fun h => π h.1.length h.2

/-- The distribution of the observable history at epoch n, constructed from the
actual transition and action distributions; n=0 precedes the first reward. -/
noncomputable def historyLaw {S : Type*} {A : S → Type*}
    (M : Model S A) (π : HRPolicy S A) (s : S) : ℕ → PMF (History S A)
  | 0 => PMF.pure ([], s)
  | n + 1 => (historyLaw M π s n).bind fun h =>
      (π h).bind fun a => (M.transition h.2 a).bind fun t =>
        PMF.pure (h.1 ++ [⟨h.2, a⟩], t)

/-- Expected accumulated nonnegative stage rewards, computed using the finite
history laws. ENNReal sums retain divergence as +∞. The generic payoff g may
itself equal +∞, including at a single state/action; zero probability times
this infinite payoff is zero. The later reward-part definitions specialize g
to finite one-step values, but that is not a restriction of this helper. -/
noncomputable def accumulated {S : Type*} {A : S → Type*}
    (M : Model S A) (π : HRPolicy S A) (s : S)
    (g : (t : S) → A t → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' n : ℕ, ∑' h : History S A, ∑' a : A h.2,
    historyLaw M π s n h * π h a * g h.2 a

noncomputable def positiveReward {S : Type*} {A : S → Type*}
    (M : Model S A) (π : HRPolicy S A) (s : S) : ℝ≥0∞ :=
  accumulated M π s (fun t a => ENNReal.ofReal (M.reward t a))

noncomputable def negativeReward {S : Type*} {A : S → Type*}
    (M : Model S A) (π : HRPolicy S A) (s : S) : ℝ≥0∞ :=
  accumulated M π s (fun t a => ENNReal.ofReal (-M.reward t a))

/-- Assumption 7.1.1: at least one expected reward part is finite, separately
for every history-dependent randomized policy and starting state. -/
def WellDefined {S : Type*} {A : S → Type*} (M : Model S A) : Prop :=
  ∀ (π : HRPolicy S A) (s : S),
    positiveReward M π s < ⊤ ∨ negativeReward M π s < ⊤

/-- Total expected reward, used only under WellDefined or PositiveBounded.
The excluded case +∞−+∞ has EReal's totalized value, not a reward interpretation. -/
noncomputable def policyValue {S : Type*} {A : S → Type*}
    (M : Model S A) (π : HRPolicy S A) (s : S) : EReal :=
  (positiveReward M π s : EReal) - (negativeReward M π s : EReal)

/-- Equation (7.1.3): the supremum over all admissible HR policies, separately
at each initial state. Extended suprema preserve unbounded values. -/
noncomputable def optimalValue {S : Type*} {A : S → Type*}
    (M : Model S A) (s : S) : EReal :=
  ⨆ π : HRPolicy S A, policyValue M π s

/-- Exactly Assumptions 7.2.1 and 7.2.2. No uniform upper bound, optimal
policy, nonnegative reward for every action, or Bellman identity is assumed. -/
def PositiveBounded {S : Type*} {A : S → Type*} (M : Model S A) : Prop :=
  (∀ (π : HRPolicy S A) (s : S), positiveReward M π s < ⊤) ∧
  (∀ s : S, ∃ a : A s, 0 ≤ M.reward s a)

end PutermanMDP.TotalReward

import Mathlib
import Definitions.Def_PutermanMDP_TotalReward_Model
open scoped ENNReal

namespace PutermanMDP.TotalReward

/-- Expectation of an extended value under a discrete probability distribution,
as the difference of nonnegative expectations. Bellman results below apply this
only to nonnegative values, where the negative expectation is zero. -/
noncomputable def transitionValue {S : Type*} (p : PMF S) (v : S → EReal) : EReal :=
  ((∑' t : S, p t * (v t).toENNReal : ℝ≥0∞) : EReal) -
    ((∑' t : S, p t * (-v t).toENNReal : ℝ≥0∞) : EReal)

/-- Component form of the undiscounted optimality operator (7.1.5).
The supremum is over all admissible actions; attainment is not required. -/
noncomputable def bellman {S : Type*} {A : S → Type*}
    (M : Model S A) (v : S → EReal) (s : S) : EReal :=
  ⨆ a : A s, (M.reward s a : EReal) + transitionValue (M.transition s a) v

/-- The pointwise-finite nonnegative class V⁺ on p. 285. It is not the class
of uniformly bounded functions. Bellman is not assumed to preserve this class. -/
def InVPlus {S : Type*} (v : S → EReal) : Prop :=
  ∀ s : S, 0 ≤ v s ∧ v s < ⊤

/-- The actual recurrence in Theorem 7.2.12, with the initial vector exactly zero.
Extended values make this a total definition without defaulting divergent sums to zero. -/
noncomputable def valueIterate {S : Type*} {A : S → Type*}
    (M : Model S A) : ℕ → S → EReal
  | 0 => fun _ => 0
  | n + 1 => bellman M (valueIterate M n)

end PutermanMDP.TotalReward
-/

namespace PutermanMDP.TotalReward

/-- Theorem 7.2.12: the zero-start Bellman iterates converge pointwise and
monotonically to the expected-total-reward optimum. Finiteness is a conclusion,
not a uniform bound or an assumption on the Bellman orbit. -/
theorem value_iteration {S : Type*} {A : S → Type*}
    [Countable S] [Nonempty S] [∀ s, Countable (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) (hM : PositiveBounded M) :
    (∀ n : ℕ, InVPlus (valueIterate M n)) ∧
    ∀ s : S, ∃ l : ℝ, optimalValue M s = (l : EReal) ∧
      Monotone (fun n : ℕ => valueIterate M n s) ∧
      Filter.Tendsto (fun n : ℕ => valueIterate M n s) Filter.atTop (nhds (l : EReal)) := by sorry

end PutermanMDP.TotalReward
