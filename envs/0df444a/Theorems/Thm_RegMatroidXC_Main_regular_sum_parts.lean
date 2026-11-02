-- Prove2me | Theorems.Thm_RegMatroidXC_Main_regular_sum_parts
-- name    : RegMatroidXC.Main.regular_sum_parts
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-01T11:36:37.797195+00:00
-- url     : https://prove2.me/theorems/7221c74e-103d-4a64-882f-164f4c6b2416
-- title:
--   Parts of a 1-sum or 2-sum of a regular matroid are regular
-- statement:
--   Let $M$ be a regular matroid with finite ground set, and suppose $M$ is a 1-sum or a 2-sum of the matroids $M_1$ and $M_2$:
--   $$M = M_1 \oplus_1 M_2 \quad\text{or}\quad M = M_1 \oplus_2 M_2,$$
--   in the sense of Seymour used by Aprile and Fiorini (p. 3): $M_1, M_2$ are binary, $E(M) = E(M_1)\,\Delta\,E(M_2)$, the cycles of $M$ are exactly the sets $C_1 \Delta C_2 \subseteq E(M)$ with $C_i$ a cycle of $M_i$, and
--
--   1. for a 1-sum, $E(M_1)$ and $E(M_2)$ are disjoint and nonempty;
--   2. for a 2-sum, $E(M_1) \cap E(M_2) = \{a\}$, where $a$ is neither a loop nor a coloop of $M_1$ or of $M_2$, and $|E(M_1)|, |E(M_2)| \ge 3$.
--
--   Then both parts are regular:
--   $$M_1 \text{ and } M_2 \text{ are regular.}$$
--
--   This is the closure property used in the 1-sum/2-sum case of the proof of Theorem 1 of Aprile–Fiorini ("assume that $M$ is a 1- or 2-sum of regular matroids $M_1$ and $M_2$"): the parts of a 1- or 2-sum are isomorphic to minors of the sum, and the class of regular matroids is closed under minors and isomorphism, so the induction hypothesis applies to the parts.
--
--   **Formalization Note** Regularity is the published `IsRegular` (representable over $\mathbb R$ by a totally unimodular matrix), and the sums are the published `IsOneSum`/`IsTwoSum`. The ground set of $M$ is assumed finite (as everywhere in the mission); the ground sets of the parts are then finite as well.
-- source:
--   Aprile & Fiorini, Regular Matroids Have Polynomial Extension Complexity, arXiv:1909.08539v2, proof of Theorem 1 (p. 4, 1-/2-sum case); the parts are minors of the sum: Oxley, Matroid Theory (2nd ed., 2011), Proposition 7.1.21, and regular matroids are minor-closed (Oxley, Section 6.6)

import Mathlib
import Definitions.Def_RegMatroidXC_Main_Matroids
import Definitions.Def_RegMatroidXC_Main_Sums

namespace RegMatroidXC.Main

theorem regular_sum_parts (α : Type) (M M₁ M₂ : Matroid α) [Fintype M.E] (hreg : IsRegular M)
    (hsum : IsOneSum M M₁ M₂ ∨ IsTwoSum M M₁ M₂) : IsRegular M₁ ∧ IsRegular M₂ := by sorry

end RegMatroidXC.Main
