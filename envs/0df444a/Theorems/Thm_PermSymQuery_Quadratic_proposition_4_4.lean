-- Prove2me | Theorems.Thm_PermSymQuery_Quadratic_proposition_4_4
-- name    : PermSymQuery.Quadratic.proposition_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:14.703526+00:00
-- url     : https://prove2.me/theorems/2bd1dc69-96d0-410a-9cbd-d8e4f073e361
-- title:
--   Proposition 4.4 — bias-preserving nonadaptive simulation
-- statement:
--   There is one positive absolute natural constant $C$ with the following property. Let $N$ be any natural number, $A$ any finite alphabet, $\mathrm{enc}:A\to\{0,1\}^b$ any injective encoding, $D\subseteq A^N$ any promise and $f:A^N\to\{0,1\}$ permutation-invariant on $D$. Let $T\ge1$ and $0<\beta\le1/2$. Suppose a quantum algorithm with any finite workspace and $T'\le T$ queries satisfies $\Pr[\mathcal A(x)=f(x)]\ge1/2+\beta$ on every $x\in D$. Then there is a nonadaptive randomized decision tree $R$ such that
--   $$\operatorname{queries}(R)\le CT^2,\qquad\Pr[R(x)=f(x)]\ge\frac12+\frac{3\beta}{4}\quad(x\in D).$$
--   The cost bound holds for every input and every tree in the support, and each supported tree's whole query list is input-independent. Classical queries read alphabet symbols at actual positions, with no dummy queries charged. The same constant works for all $N,A,b,\mathrm{enc},D,f,T,\beta$ and quantum algorithms. This is the bias-preserving simulation used by the goal theorem.
--
--   Differences from the source:
--   - encoding: positions [N], bit strings, a partial Boolean function on D → Fin N, Fin b → ZMod 2, and a Bool-valued total extension used only on D; reason: these are relabelings and extensions representing every source instance, including empty data
--   - encoding: arbitrary finite quantum workspaces and two-outcome measurements → published QueryAlg with a Boolean computational-basis output map and arbitrary finite workspace; reason: input-independent final unitaries and ancillary registers realize every source measurement without additional queries
--   - encoding: randomized algorithms with worst-case cost and an absolute O(T²) bound → PMFs over decision trees, with supportwise cost and nonadaptivity, and one positive natural C quantified first; reason: bounded-depth trees over finite alphabets have finitely many behaviors, and a positive absolute real constant can be rounded up
-- source:
--   Yunqi Huang, Lvzhou Li, Zekun Ye, Shenggen Zheng, Optimal Separations Between Randomized and Quantum Query Complexity under Permutation Symmetry, STOC 2027 submission #1644 (October 2026), Proposition 4.4, PDF p. 19 (printed p. 17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1644.pdf

import Mathlib
import Definitions.Def_PermSymQuery_Quadratic_Model

namespace PermSymQuery.Quadratic

/-- Proposition 4.4, PDF p.19 (printed p.17): one absolute constant, nonadaptive
simulation and the exact success probability 1/2 + 3β/4. -/
theorem proposition_4_4 : ∃ C : ℕ, 0 < C ∧
    ∀ (N : ℕ) (A : Type) [Fintype A] [DecidableEq A] (b : ℕ)
      (enc : A → Bits b), Function.Injective enc →
    ∀ (D : Set (Fin N → A)) (f : (Fin N → A) → Bool), PermInvariant D f →
    ∀ (T : ℕ), 1 ≤ T → ∀ (β : ℝ), 0 < β → β ≤ 1 / 2 →
    ∀ (W : Type) [Fintype W] [DecidableEq W] (T' : ℕ), T' ≤ T →
    ∀ (alg : QAlgorithms.QueryAlg (Option (Fin N)) (Bits b) W T')
      (out : StateIndex N b W → Bool),
      (∀ x ∈ D, (1 : ℝ) / 2 + β ≤ alg.outputProb (inputOracle enc x) out (f x)) →
      ∃ R : QAlgorithms.RandDecisionTree (Fin N) A Bool,
        Nonadaptive R ∧ QAlgorithms.RandMakesAtMost R (C * T ^ 2) ∧
        ∀ x ∈ D, (1 : ℝ) / 2 + 3 * β / 4 ≤ QAlgorithms.successProb R x (f x) := by sorry

end PermSymQuery.Quadratic
