-- Prove2me | Theorems.Thm_PutermanMDP_FiniteHorizon_markov_suffices
-- name    : PutermanMDP.FiniteHorizon.markov_suffices
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:31:43.182876+00:00
-- url     : https://prove2.me/theorems/cbcbca59-bbc7-4eb6-b626-3b0920f424d5
-- title:
--   Theorem 4.4.2 — deterministic Markov policies suffice
-- statement:
--   Let $u_t$ solve the history optimality equations and terminal condition in a bounded-reward discrete finite-horizon model. Three conclusions hold.
--
--   1. For each $0\le t\le H$, $u_t(h_t)$ depends on the history only through its last state: histories of equal length with the same current state have equal values.
--   2. For every $\varepsilon>0$, there is one deterministic Markov policy $d$ satisfying
--   $$
--   v^*(s)<v^d(s)+\varepsilon\qquad\text{for every initial state }s.
--   $$
--   3. If a maximizing action exists in the one-step optimality expression at every nonterminal history, a deterministic Markov policy is optimal among all history-dependent randomized policies.
--
--   This distinguishes approximate optimality, which needs no maximizer, from exact optimality under attainment.
--
--   **Formalization Note** $H=N-1$. In the attainment premise, histories index the expression in (4.4.1); the first conclusion makes this equivalent to attainment at each state and epoch. The policy is a single time-dependent state rule, chosen simultaneously for all initial states.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 89 (PDF 105), Theorem 4.4.2; Eq. (4.4.1); https://doi.org/10.1002/9780470316887.ch4

import Mathlib
import Definitions.Def_PutermanMDP_FiniteHorizon_BellmanSolution

namespace PutermanMDP.FiniteHorizon

theorem markov_suffices {S A : Type} [Countable S] [Nonempty S]
    (M : Model S A) (u : History S A → ℝ) (hu : BellmanSolution M u) :
    (∀ h g : History S A, h.time ≤ M.horizon → h.time = g.time →
      h.state = g.state → u h = u g) ∧
    (∀ ε : ℝ, 0 < ε → ∃ d : MarkovPolicy M, IsEpsilonOptimal M ε d.randomized) ∧
    ((∀ h : History S A, h.time < M.horizon →
        ∃ a, historyScore M u h a = u h) →
      ∃ d : MarkovPolicy M, IsOptimal M d.randomized) := by sorry

end PutermanMDP.FiniteHorizon

/- Imported definition source snapshots for a self-contained offline audit.

import Mathlib

namespace PutermanMDP.FiniteHorizon

/-- A history consists of past state-action pairs in chronological order and the current state.
Its list length is the zero-based current epoch. No positive-probability restriction is imposed. -/
structure History (S A : Type) where
  past : List (S × A)
  state : S

def History.time {S A : Type} (h : History S A) : ℕ := h.past.length

def History.initial {S A : Type} (s : S) : History S A := ⟨[], s⟩

def History.extend {S A : Type} (h : History S A) (a : A) (j : S) : History S A :=
  ⟨h.past ++ [(h.state, a)], j⟩

/-- `horizon` counts decisions. The terminal epoch is `horizon`, corresponding to epoch
`N = horizon + 1` under one-based indexing. Rewards may have either sign. -/
structure Model (S A : Type) [Countable S] where
  horizon : ℕ
  available : S → Set A
  available_nonempty : ∀ s, (available s).Nonempty
  transition : ℕ → (s : S) → {a // a ∈ available s} → PMF S
  reward : ℕ → (s : S) → {a // a ∈ available s} → ℝ
  terminal : S → ℝ
  bounded : ∃ C : ℝ, 0 ≤ C ∧
    (∀ t, t < horizon → ∀ s a, |reward t s a| ≤ C) ∧
    (∀ s, |terminal s| ≤ C)

/-- All history-dependent randomized decision rules, extended harmlessly beyond the horizon. -/
def Policy {S A : Type} [Countable S] (M : Model S A) : Type :=
  (h : History S A) → PMF {a // a ∈ M.available h.state}

def HistoryPolicy {S A : Type} [Countable S] (M : Model S A) : Type :=
  (h : History S A) → {a // a ∈ M.available h.state}

def MarkovPolicy {S A : Type} [Countable S] (M : Model S A) : Type :=
  ℕ → (s : S) → {a // a ∈ M.available s}

noncomputable def HistoryPolicy.randomized {S A : Type} [Countable S] {M : Model S A}
    (d : HistoryPolicy M) : Policy M := fun h => PMF.pure (d h)

noncomputable def MarkovPolicy.randomized {S A : Type} [Countable S] {M : Model S A}
    (d : MarkovPolicy M) : Policy M := fun h => PMF.pure (d h.time h.state)

end PutermanMDP.FiniteHorizon

import Mathlib
import Definitions.Def_PutermanMDP_FiniteHorizon_Model

namespace PutermanMDP.FiniteHorizon

/-- The probability law of the sum of the next `k` decision rewards and the terminal reward.
At each decision, sample the policy's action, then the transition's state. The recursion
pushes forward the future reward law by adding the immediate reward; it does not evaluate
expectations or optimize policies. -/
noncomputable def rewardLaw {S A : Type} [Countable S] (M : Model S A) (π : Policy M) :
    ℕ → History S A → PMF ℝ
  | 0, h => PMF.pure (M.terminal h.state)
  | k + 1, h => (π h).bind fun a =>
      (M.transition h.time h.state a).bind fun j =>
        (rewardLaw M π k (h.extend a.val j)).map
          (fun z => M.reward h.time h.state a + z)

/-- The expectation of the actual remaining reward law. It is used only for `h.time ≤ horizon`.
The bounded reward assumption then implies integrability and a uniform bound over policies. -/
noncomputable def continuationValue {S A : Type} [Countable S]
    (M : Model S A) (π : Policy M) (h : History S A) : ℝ :=
  ∫ z : ℝ, z ∂(rewardLaw M π (M.horizon - h.time) h).toMeasure

noncomputable def totalValue {S A : Type} [Countable S]
    (M : Model S A) (π : Policy M) (s : S) : ℝ :=
  continuationValue M π (History.initial s)

/-- The supremum is over all history-dependent randomized policies, not merely Markov rules.
Nonempty action fibers give policies, and bounded finite-horizon rewards bound this range. -/
noncomputable def optimalContinuation {S A : Type} [Countable S]
    (M : Model S A) (h : History S A) : ℝ :=
  ⨆ π : Policy M, continuationValue M π h

noncomputable def optimalTotal {S A : Type} [Countable S] (M : Model S A) (s : S) : ℝ :=
  ⨆ π : Policy M, totalValue M π s

def IsOptimal {S A : Type} [Countable S] (M : Model S A) (π : Policy M) : Prop :=
  ∀ s, ∀ ρ : Policy M, totalValue M ρ s ≤ totalValue M π s

/-- Strict epsilon optimality, simultaneously for every initial state. -/
def IsEpsilonOptimal {S A : Type} [Countable S] (M : Model S A)
    (ε : ℝ) (π : Policy M) : Prop :=
  ∀ s, optimalTotal M s < totalValue M π s + ε

/-- The separate randomized policy evaluation algorithm: terminal initialization followed
by the action-averaged one-step recurrence, repeated exactly `k` times. -/
noncomputable def evaluate {S A : Type} [Countable S] (M : Model S A) (π : Policy M) :
    ℕ → History S A → ℝ
  | 0, h => M.terminal h.state
  | k + 1, h => ∑' a, (π h a).toReal *
      (M.reward h.time h.state a +
        ∑' j, (M.transition h.time h.state a j).toReal *
          evaluate M π k (h.extend a.val j))

end PutermanMDP.FiniteHorizon

import Mathlib
import Definitions.Def_PutermanMDP_FiniteHorizon_continuationValue

namespace PutermanMDP.FiniteHorizon

/-- The model parameter in every definition in this module includes the common bound
`∃ C ≥ 0, (∀ t < M.horizon, ∀ s a, |M.reward t s a| ≤ C) ∧
(∀ s, |M.terminal s| ≤ C)` through `Model.bounded`. In particular these predicates
are defined on bounded-reward models, not on arbitrary unbounded transition-reward data.
This score is the immediate reward plus the next-state weighted continuation. -/
noncomputable def historyScore {S A : Type} [Countable S] (M : Model S A)
    (u : History S A → ℝ) (h : History S A) (a : {a // a ∈ M.available h.state}) : ℝ :=
  M.reward h.time h.state a +
    ∑' j, (M.transition h.time h.state a j).toReal * u (h.extend a.val j)

/-- A real solution of the history optimality equations with terminal boundary data.
`IsLUB` means a genuine finite supremum, avoiding the default value of an unbounded real sup. -/
def BellmanSolution {S A : Type} [Countable S] (M : Model S A)
    (u : History S A → ℝ) : Prop :=
  (∀ h, h.time = M.horizon → u h = M.terminal h.state) ∧
  (∀ h, h.time < M.horizon → IsLUB (Set.range (historyScore M u h)) (u h))

/-- The maximum form of the same equations, including attainment at every history. -/
def MaxBellmanSolution {S A : Type} [Countable S] (M : Model S A)
    (u : History S A → ℝ) : Prop :=
  (∀ h, h.time = M.horizon → u h = M.terminal h.state) ∧
  (∀ h, h.time < M.horizon → IsGreatest (Set.range (historyScore M u h)) (u h))

noncomputable def stateScore {S A : Type} [Countable S] (M : Model S A)
    (u : ℕ → S → ℝ) (t : ℕ) (s : S) (a : {a // a ∈ M.available s}) : ℝ :=
  M.reward t s a + ∑' j, (M.transition t s a j).toReal * u (t + 1) j

/-- The backward induction algorithm as its exact output recurrence: terminal initialization
and an attained maximum at every preceding epoch and state. No value or optimality condition
is included in this predicate. -/
def BackwardSolution {S A : Type} [Countable S] (M : Model S A)
    (u : ℕ → S → ℝ) : Prop :=
  (∀ s, u M.horizon s = M.terminal s) ∧
  (∀ t, t < M.horizon → ∀ s, IsGreatest (Set.range (stateScore M u t s)) (u t s))

/-- All maximizing actions, constructed directly from the one-step expression. -/
def maximizingActions {S A : Type} [Countable S] (M : Model S A)
    (u : ℕ → S → ℝ) (t : ℕ) (s : S) : Set {a // a ∈ M.available s} :=
  {a | ∀ b, stateScore M u t s b ≤ stateScore M u t s a}

end PutermanMDP.FiniteHorizon
-/
