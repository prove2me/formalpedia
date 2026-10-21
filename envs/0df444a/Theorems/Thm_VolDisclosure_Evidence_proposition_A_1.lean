-- Prove2me | Theorems.Thm_VolDisclosure_Evidence_proposition_A_1
-- name    : VolDisclosure.Evidence.proposition_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:03.376534+00:00
-- url     : https://prove2.me/theorems/693c73ea-cb01-4d10-a9ea-b841ecaeb218
-- title:
--   Proposition A.1, p. 38 — the fixed point s of T exists, is unique, increasing, concave, and equals s* from (1+r)pδ/r on
-- statement:
--   Fix parameters satisfying the standing assumptions of §3 and an evidence probability $\pi \in [0,1)$. Then:
--
--   1. the Bellman operator (T) has a fixed point $s$ in $\mathcal F$ (a firm value);
--   2. it is unique: any two firm values agree on $\mathbb R_+$;
--   3. every firm value $s$ is nondecreasing and concave on $\mathbb R_+$ and satisfies
--   $$
--   s(v) = s^* \qquad\text{for all } v \ge \frac{(1+r)p\delta}{r}.
--   $$
--
--   This is the existence and shape result on which every later statement about the firm value $s(\cdot)$ rests.
--
--   **Formalization Note.** "Increasing" is read as nondecreasing, since $s$ is constant equal to $s^*$ beyond $\bar v$. Uniqueness is stated on $\mathbb R_+$, where firm values are defined; values at negative arguments never enter the model.
-- source:
--   Fu & Trigilia, Voluntary Disclosure, Moral Hazard and Default Risk, working paper (August 28, 2019), p. 38, Proposition A.1

import Mathlib
import Definitions.Def_VolDisclosure_Evidence_Model

namespace VolDisclosure.Evidence

/-- Proposition A.1 (p. 38): (T) has a fixed point in `F`, unique on `R₊`; it is increasing,
concave, and equal to `s*` from `(1+r)pδ/r` on. -/
theorem proposition_A_1 (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π < 1) :
    (∃ s, IsValue P π s) ∧
    (∀ s s' : ℝ → ℝ, IsValue P π s → IsValue P π s' → ∀ v, 0 ≤ v → s v = s' v) ∧
    ∀ s : ℝ → ℝ, IsValue P π s →
      MonotoneOn s (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) s ∧
      ∀ v, P.vBar ≤ v → s v = P.sStar := by sorry

end VolDisclosure.Evidence
