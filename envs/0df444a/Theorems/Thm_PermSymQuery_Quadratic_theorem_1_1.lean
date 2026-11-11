-- Prove2me | Theorems.Thm_PermSymQuery_Quadratic_theorem_1_1
-- name    : PermSymQuery.Quadratic.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:25.197444+00:00
-- url     : https://prove2.me/theorems/3e8eb878-0159-448a-aedf-79b101186e1f
-- title:
--   Theorem 1.1 — quadratic randomized versus quantum query complexity
-- statement:
--   There is one positive absolute natural constant $C$ such that, for every natural input length $N$, every finite alphabet $A$, every binary encoding length $b$, every injective encoding $\mathrm{enc}:A\to\{0,1\}^b$, every promise $D\subseteq A^N$, every Boolean function $f$ on that promise invariant under all permutations of input positions, and every $1/6\le\varepsilon<1/2$,
--   $$R_\varepsilon(f)\le C\,Q_\varepsilon(f)^2.$$
--   Both complexities use error at most $\varepsilon$ on every promised input and worst-case query cost. Quantum algorithms allow arbitrary finite workspaces and input-independent computation; the oracle XORs the entire encoded symbol in one query. Classical algorithms read one alphabet symbol per query. The constant is independent of the error, the alphabet, the encoding and all other instance data. Empty promises, empty alphabets and $N=0$ are included. This is the paper's full quadratic upper bound; nonadaptivity is required in Proposition 4.4 but is not added to the goal.
--
--   Differences from the source:
--   - encoding: positions [N], bit strings, a partial Boolean function on D → Fin N, Fin b → ZMod 2, and a Bool-valued total extension used only on D; reason: these are relabelings and extensions representing every source instance, including empty data
--   - encoding: arbitrary finite quantum workspaces and two-outcome measurements → published QueryAlg with a Boolean computational-basis output map and arbitrary finite workspace; reason: input-independent final unitaries and ancillary registers realize every source measurement without additional queries
--   - encoding: minimum worst-case query budgets and an absolute O constant → infima in ℕ∞ and one positive natural constant quantified first; reason: an infeasible budget set gives infinity, every nonempty set of natural budgets has a least element, and rounding a positive absolute constant up preserves the bound
-- source:
--   Yunqi Huang, Lvzhou Li, Zekun Ye, Shenggen Zheng, Optimal Separations Between Randomized and Quantum Query Complexity under Permutation Symmetry, STOC 2027 submission #1644 (October 2026), Theorem 1.1 (also restated PDF p.20, printed p.18), PDF p. 4 (printed p. 2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1644.pdf

import Mathlib
import Definitions.Def_PermSymQuery_Quadratic_Model

namespace PermSymQuery.Quadratic

/-- Theorem 1.1, PDF p.4 (printed p.2), restated PDF p.20 (printed p.18).
The constant is independent of the alphabet, encoding, promise, input length and error. -/
theorem theorem_1_1 : ∃ C : ℕ, 0 < C ∧
    ∀ (N : ℕ) (A : Type) [Fintype A] [DecidableEq A] (b : ℕ)
      (enc : A → Bits b), Function.Injective enc →
    ∀ (D : Set (Fin N → A)) (f : (Fin N → A) → Bool), PermInvariant D f →
    ∀ ε : ℝ, 1 / 6 ≤ ε → ε < 1 / 2 →
      Reps D f ε ≤ (C : ℕ∞) * (Qeps enc D f ε) ^ 2 := by sorry

end PermSymQuery.Quadratic
