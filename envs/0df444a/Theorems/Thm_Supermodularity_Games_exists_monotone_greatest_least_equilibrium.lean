-- Prove2me | Theorems.Thm_Supermodularity_Games_exists_monotone_greatest_least_equilibrium
-- name    : Supermodularity.Games.exists_monotone_greatest_least_equilibrium
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-18T05:33:57.559075+00:00
-- url     : https://prove2.me/theorems/2fc4c704-b6a5-42cd-8932-8f4e9e0ee2ff
-- title:
--   Theorem 4.2.2 - the greatest and least equilibrium points increase with a parameter
-- statement:
--   Let $T$ be a partially ordered set and, for each $t \in T$, let $(N, S^t, \{f_i^t :
--   i \in N\})$ be a **supermodular game**: $S^t$ is nonempty and compact for every $t$,
--   and $S^t$ is **increasing in $t$** on $T$ (in the induced set ordering $\sqsubseteq$
--   of chunk `01-lattices`). For each player $i$ and each $x_{-i} \in S^t_{-i}$, the
--   payoff $f_i^t(y_i, x_{-i})$ is upper semicontinuous in $y_i$ on $S^t_i(x_{-i})$ for
--   every $t$, and has **increasing differences** in $(y_i, t)$ on
--   $\big(\bigcup_{t \in T} S^t_i\big) \times T$.
--
--   Then for every $t \in T$ there exist a greatest equilibrium point $g(t)$ and a least
--   equilibrium point $l(t)$ of game $t$, and $g$ and $l$ are each **increasing
--   (monotone) functions of $t$** on $T$: as the parameter $t$ increases, the greatest
--   (respectively least) equilibrium point increases.
--
--   This is Theorem 4.2.2. Milgrom and Roberts [1990a] and Sobel [1988] independently
--   establish versions of this result. Its proof cites chunk `01-lattices`'s Theorem
--   2.5.2 (the parametric extension of Zhou's fixed point theorem) directly, applied to
--   the best joint response correspondence $Y(x, t)$ across the whole parameterized
--   family of games at once.
--
--   **Formalization Note** $g$ and $l$ are packaged as genuine functions $T \to
--   \prod_i (\mathrm{Fin}\ m_i \to \mathbb{R})$, not per-$t$ existential selections,
--   since the greatest/least equilibrium point at each $t$ is unique — the standard way
--   to state "there exists a greatest fixed point, and it is increasing in the
--   parameter" in dependent type theory, matching chunk `01-lattices`'s
--   `parametrized_fixed_point_monotone`. The increasing-differences hypothesis is stated
--   on the union $\bigcup_{t} S^t_i$ of the sections across all parameters (rather than
--   on all of $(\mathrm{Fin}\ m_i \to \mathbb{R}) \times T$), matching the book's own
--   domain $\big(\bigcup_{t \in T} S^t_i\big) \times T$.
--
--   **Moderator's note.** The increasing-differences hypothesis in $(y_i, t)$ is stated on $\big(\bigcup_t S^t_i\big) \times T$ with $S^t_i$ the projection of $S^t$, for each $x_{-i} \in \bigcup_t S^t_{-i}$, as in the book's statement.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 183-184, Theorem 4.2.2

import Mathlib
import Definitions.Def_Supermodularity_Games_IsSupermodularGame
import Definitions.Def_Supermodularity_Games_IsEquilibrium
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

namespace Supermodularity.Games

theorem exists_monotone_greatest_least_equilibrium {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ι → ℕ} {T : Type*} [PartialOrder T]
    (S : T → Set (∀ i, Fin (m i) → ℝ)) (f : T → ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : ∀ t, IsSupermodularGame (S t) (f t))
    (hSne : ∀ t, (S t).Nonempty) (hScompact : ∀ t, IsCompact (S t))
    (hSinc : ∀ ⦃t t' : T⦄, t ≤ t' →
      Supermodularity.Lattices.InducedSetOrder (S t) (S t'))
    (husc : ∀ t i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f t i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S t})
    (hdiff : ∀ i, ∀ x ∈ (⋃ t : T, projOthers (S t) i),
      Supermodularity.Monotonicity.IncreasingDifferencesOn
        (fun (y : Fin (m i) → ℝ) (t : T) => f t i (Function.update x i y))
        ((⋃ t : T, proj (S t) i) ×ˢ (Set.univ : Set T))) :
    ∃ g l : T → (∀ i, Fin (m i) → ℝ),
      (∀ t, IsGreatest {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium (S t) (f t) x'} (g t)) ∧
      (∀ t, IsLeast {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium (S t) (f t) x'} (l t)) ∧
      Monotone g ∧ Monotone l := by sorry

end Supermodularity.Games
