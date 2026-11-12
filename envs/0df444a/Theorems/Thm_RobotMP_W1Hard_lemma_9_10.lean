-- Prove2me | Theorems.Thm_RobotMP_W1Hard_lemma_9_10
-- name    : RobotMP.W1Hard.lemma_9_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:42:51.505374+00:00
-- url     : https://prove2.me/theorems/3fd4ed1c-e77d-4566-a7fc-c325e4c873de
-- title:
--   Lemma 9.10 — the tester set S′ is bimonotone
-- statement:
--   Let $n \in \mathbb N$ and $S \subseteq \{0, \dots, n^2 - 1\}$. The tester set
--   $$S' = \{(z_1, w_1) \in \{0, \dots, n^2 - 1\} \times \{0, \dots, n^2\} : w_1 \ge z_1 \text{ and } (z_1 = w_1 \Rightarrow z_1 \in S)\}$$
--   is a bimonotone subset of $\{0, \dots, n^2 - 1\} \times \{0, \dots, n^2\}$.
--
--   So the tester's constraint $(z_1, w_1) \in S'$ is a legitimate CMS constraint for an arbitrary set $S$.
--
--   Differences from the source: none.
-- source:
--   Agarwal, Holmgren, Stade, Near-Optimal Makespan and Parameterized Hardness for Multi-Robot Motion Planning, STOC 2027 submission (manuscript sha256 17b4fe59…), p. 52, Lemma 9.10

import Mathlib
import Definitions.Def_RobotMP_W1Hard_Bimonotone
import Definitions.Def_RobotMP_W1Hard_Gadgets

set_option autoImplicit false

namespace RobotMP.W1Hard

open Set

/-- Lemma 9.10: for `S ⊆ {0, …, n² − 1}`, the tester set `S'` is a bimonotone subset of
`{0, …, n² − 1} × {0, …, n²}`. -/
theorem lemma_9_10 (n : ℕ) (S : Set ℤ) (hS : S ⊆ Icc 0 ((n : ℤ) ^ 2 - 1)) :
    IsBimonotone (Icc 0 ((n : ℤ) ^ 2 - 1)) (Icc 0 ((n : ℤ) ^ 2)) (testerSet n S) := by sorry

end RobotMP.W1Hard
