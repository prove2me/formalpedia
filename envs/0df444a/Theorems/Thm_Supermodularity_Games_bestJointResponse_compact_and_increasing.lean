-- Prove2me | Theorems.Thm_Supermodularity_Games_bestJointResponse_compact_and_increasing
-- name    : Supermodularity.Games.bestJointResponse_compact_and_increasing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:32:34.686288+00:00
-- url     : https://prove2.me/theorems/4625d32c-f72e-4d06-a4df-916b3b953863
-- title:
--   Lemma 4.2.2(b),(f) - the best joint response is a nonempty compact sublattice and increasing
-- statement:
--   Consider a supermodular game $(N, S, \{f_i\})$ for which $S$ is nonempty and compact
--   and each $f_i(y_i, x_{-i})$ is upper semicontinuous in $y_i$ on $S_i(x_{-i})$ for
--   each $x_{-i} \in S_{-i}$ and each $i$. Then:
--
--   (b) The set $Y(x)$ of best joint responses is a nonempty compact sublattice of
--       $\mathbb{R}^m$ for every $x \in S$; and
--
--   (f) The best joint response correspondence $Y$ is **increasing** in $x$ on $S$:
--       $x \preceq x'$ (both in $S$) implies $Y(x) \sqsubseteq Y(x')$ in the induced set
--       ordering $\sqsubseteq$ of chunk `01-lattices`.
--
--   These are parts (b) and (f) of Lemma 4.2.2, the two of its eight parts used directly
--   in the proof of Theorem 4.2.1 (the goal): part (b) supplies the subcomplete-valued
--   hypothesis of Theorem 2.5.1 (every compact sublattice of $\mathbb{R}^m$ is
--   subcomplete, by Theorem 2.3.1 of chunk `01-lattices`), and part (f) supplies its
--   increasing-correspondence hypothesis.
--
--   **Formalization Note** Only parts (b) and (f) are formalized, per the chunk brief's
--   instruction to transcribe only the parts a proof of the goal actually uses; parts
--   (a), (c)-(e), (g), (h) of Lemma 4.2.2 (about the *individual* best-response sets
--   $Y_i(x_{-i})$, and about greatest/least selections) are left out of this mission.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 180, Lemma 4.2.2, parts (b) and (f)

import Mathlib
import Definitions.Def_Supermodularity_Games_IsSupermodularGame
import Definitions.Def_Supermodularity_Games_BestJointResponse
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

namespace Supermodularity.Games

theorem bestJointResponse_compact_and_increasing {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ι → ℕ} (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : IsSupermodularGame S f) (hSne : S.Nonempty) (hScompact : IsCompact S)
    (husc : ∀ i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S}) :
    (∀ x ∈ S, (BestJointResponse S f x).Nonempty ∧ IsCompact (BestJointResponse S f x) ∧
      IsSublattice (BestJointResponse S f x)) ∧
    ∀ ⦃x x' : ∀ i, Fin (m i) → ℝ⦄, x ∈ S → x' ∈ S → x ≤ x' →
      Supermodularity.Lattices.InducedSetOrder (BestJointResponse S f x) (BestJointResponse S f x') := by sorry

end Supermodularity.Games
