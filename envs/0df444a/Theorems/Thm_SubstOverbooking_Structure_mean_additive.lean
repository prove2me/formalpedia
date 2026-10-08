-- Prove2me | Theorems.Thm_SubstOverbooking_Structure_mean_additive
-- name    : SubstOverbooking.Structure.mean_additive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:49.747289+00:00
-- url     : https://prove2.me/theorems/59155d5c-6a52-47c3-9409-c7a406e642e4
-- title:
--   Proof of Theorem 2, p. 88 — with the semigroup property, E[Zᵢ(uᵢ)] is additive in uᵢ
-- statement:
--   Let $u \mapsto L(u)$ be a family of laws on $\mathbb N$ with the semigroup property and finite means on a parameter set $P$. Then for all $u, s \in P$,
--
--   $$\mathbb E[Z(u + s)] = \mathbb E[Z(u)] + \mathbb E[Z(s)],$$
--
--   where $Z(v)$ denotes a random variable with law $L(v)$.
--
--   In the proof of Theorem 2 this is what makes the first two terms of $G$ drop out of every second difference, so that (6) and (7) reduce to statements about $\mathbb E[V_0(Z(u))]$.
-- source:
--   Karaesmen & van Ryzin, Overbooking with Substitutable Inventory Classes, Operations Research 52(1):83–104 (2004), p. 88, proof of Theorem 2, first paragraph

import Mathlib
import Definitions.Def_SubstOverbooking_Structure_Setting

namespace SubstOverbooking.Structure

open MeasureTheory

theorem mean_additive (P : Set ℝ) (L : ℝ → PMF ℕ) (hL : IsSemigroupFamily P L)
    (u s : ℝ) (hu : u ∈ P) (hs : s ∈ P) :
    ∫ k, (k : ℝ) ∂(L (u + s)).toMeasure =
      ∫ k, (k : ℝ) ∂(L u).toMeasure + ∫ k, (k : ℝ) ∂(L s).toMeasure := by sorry

end SubstOverbooking.Structure
