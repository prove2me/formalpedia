-- Prove2me | Theorems.Thm_TheoryOfGames_Decomposition_decomposable_iff_splitting
-- name    : TheoryOfGames.Decomposition.decomposable_iff_splitting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T04:13:19.092138+00:00
-- url     : https://prove2.me/theorems/f2a66268-6ec1-4901-b072-ac2a1595914b
-- title:
--   (42:G) — a constant-sum game is decomposable w.r.t. J, I − J iff (41:6), i.e. (41:7), holds
-- statement:
--   Let $v$ be the characteristic function of a constant-sum game on the finite set of players $I$, i.e. $v$ satisfies (42:6:a)–(42:6:c), and let $J \subseteq I$, $K = I - J$. Then the following three statements are equivalent:
--
--   1. the game is decomposable with respect to $J$ and $K$ (there are constant-sum games $\Delta$ on $J$ and $\mathrm H$ on $K$ with $v(R) = v_\Delta(R \cap J) + v_{\mathrm H}(R \cap K)$);
--   2. (41:6): $v(S \cup T) = v(S) + v(T)$ for all $S \subseteq J$, $T \subseteq K$, i.e. $J$ is a splitting set;
--   3. (41:7):
--   $$v(R) = v(R \cap J) + v(R \cap K) \quad \text{for all } R \subseteq I.$$
--
--   This is the book's explicit criterion of decomposability in the domain of all constant-sum games; in contrast with the zero-sum case (41:C), no extra conditions such as (41:8), (41:9) are needed.
--
--   **Formalization Note** Stated as a conjunction of two equivalences (1 ⇔ 2 and 2 ⇔ 3). The complement $K = I - J$ is `Jᶜ`.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 352, 42.5.2, (42:G); p. 343, (41:6), (41:7)

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting
import Definitions.Def_TheoryOfGames_Decomposition_Constituent

namespace TheoryOfGames.Decomposition

/-- (42:G), 42.5.2: in the domain of all constant-sum games, the game `v` is decomposable with
respect to `J` and `K = I - J` if and only if it fulfills the condition (41:6), i.e. (41:7):
`v(R) = v(R ∩ J) + v(R ∩ K)` for all `R ⊆ I`. -/
theorem decomposable_iff_splitting {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (J : Finset ι) :
    (IsDecomposable v J ↔ IsSplitting v J) ∧
      (IsSplitting v J ↔ ∀ R : Finset ι, v R = v (R ∩ J) + v (R ∩ Jᶜ)) := by sorry

end TheoryOfGames.Decomposition
