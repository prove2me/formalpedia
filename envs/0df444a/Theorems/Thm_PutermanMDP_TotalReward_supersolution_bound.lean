-- Prove2me | Theorems.Thm_PutermanMDP_TotalReward_supersolution_bound
-- name    : PutermanMDP.TotalReward.supersolution_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:31:53.604474+00:00
-- url     : https://prove2.me/theorems/dee39cba-9075-4d84-8b18-b4004fe27abe
-- title:
--   Theorem 7.2.2 — Nonnegative supersolutions bound the value
-- statement:
--   Consider a positive bounded model on nonempty countable state and action spaces: every policy has finite expected accumulated positive reward at each initial state, and a nonnegative-reward action is available in every state. Let $v:S\to\mathbb R$ be pointwise finite and nonnegative. If $v\ge\mathcal Lv$, then
--   $$
--   v(s)\ge v^*(s)\qquad(s\in S).
--   $$
--   Thus any nonnegative supersolution bounds the optimum over all admissible history-dependent randomized policies.
--
--   **Formalization Note** The standing assumptions of §7.2 are explicit. Lean embeds the real-valued class $V^+$ into extended-real functions by requiring $0\le v(s)<\infty$. No uniform bound on $v$ is imposed, and the Bellman inequality itself excludes an infinite positive Bellman value.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 285 (PDF 301), Theorem 7.2.2; standing Assumptions 7.2.1–7.2.2, p. 284

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

/-- Theorem 7.2.2, under the standing positive-bounded assumptions of §7.2.
Individual policy values may be −∞. The optimal value cannot be −∞ under
these hypotheses: choosing a nonnegative-reward action at every state gives
a policy with nonnegative value. This is not an added hypothesis. -/
theorem supersolution_bound {S : Type*} {A : S → Type*}
    [Countable S] [Nonempty S] [∀ s, Countable (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) (hM : PositiveBounded M)
    (v : S → EReal) (hv : InVPlus v) (hsuper : bellman M v ≤ v) :
    optimalValue M ≤ v := by sorry

end PutermanMDP.TotalReward
