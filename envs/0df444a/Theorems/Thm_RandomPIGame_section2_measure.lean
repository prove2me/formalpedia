-- Prove2me | Theorems.Thm_RandomPIGame_section2_measure
-- name    : RandomPIGame.section2_measure
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:49.963985+00:00
-- url     : https://prove2.me/theorems/e400bb0a-432f-4076-9d01-5721485343e2
-- title:
--   §2, p.8: $g$ is measurable and $\mathbb P_p$ is the unique probability measure with (2.4)–(2.5) (corrected: "unique measure" → "unique probability measure")
-- statement:
--   Let $p$ be a primitive distribution. The map $g:\Pi\to\Omega$ is Borel measurable, and its distribution $\mathbb P_p$ is a probability measure satisfying
--   $$
--   \mathbb P(E(i,k,0))=p_i(k,0),\qquad
--   \mathbb P\Big(E(i,k,n)\cap\bigcap_{j=1}^n\{\omega(j)\in B_j\}\Big)=p_i(k,n)\prod_{j=1}^n\mathbb P(B_j)
--   $$
--   for all $i\in\{\mathrm I,\mathrm{II}\}$, $k\ge0$, $n\ge1$ and Borel sets $B_1,\dots,B_n\subseteq\Omega$. Moreover, every probability measure on the Borel subsets of $\Omega$ satisfying these equalities equals $\mathbb P_p$.
--
--   This pins down the random game: the equalities say that the root's data is drawn from $p$ and that its subgames are independent copies of the whole game. The paper attributes the result essentially to Neveu.
--
--   Differences from the source:
--   - correction: there exists a unique measure P on the Borel subsets of Ω satisfying (2.4)–(2.5) → uniqueness among probability measures on Ω; reason: the printed claim is false: for p = δ(I, 1, 2) every assumption holds, and both P_p and the zero measure satisfy (2.4)–(2.5), since p_i(k, 0) = 0 and (2.5) reads 0 = p_i(k, 2)·0·0; the same page calls P the unique Borel probability measure for [1]–[2]
--   - encoding: indices j, ℓ ∈ {1, …, n} → an index j : Fin n standing for j + 1; reason: a reindexing; no instance changes
--   - encoding: ω(j) is defined on {ξ_ω(⊘) ≥ j} → Game.child is total and returns ω when (j) is not a node; reason: every use restricts to E(i, k, n) with j ≤ n or conditions on that event, so the default never matters
--   - encoding: probabilities P(·) → Measure.real, a real number; reason: all measures involved are finite, so nothing is lost
--   - encoding: capacities and thresholds k in [0, ∞) → capacities and thresholds k in ℝ≥0; reason: Lean convention; the same numbers
-- source:
--   Flesch, Predtetchinski & Suomala, Random perfect information games, arXiv:2104.10528v1, §2, p.8, (2.4)–(2.5), and "The map g is Borel measurable, and its distribution satisfies (2.4)–(2.5)."

import Mathlib
import Definitions.Def_RandomPIGame_Primitive
import Definitions.Def_RandomPIGame_Game
import Definitions.Def_RandomPIGame_Measure

open MeasureTheory

namespace RandomPIGame

/-- The map `g` is Borel measurable, its distribution `P_p` satisfies (2.4)–(2.5), and `P_p` is the
unique probability measure on the Borel subsets of `Ω` that does.
Flesch, Predtetchinski & Suomala, Random perfect information games, arXiv:2104.10528v1, §2, p.8,
(2.4)–(2.5).

**Formalization Note.** The paper prints "unique measure"; uniqueness holds among probability
measures. At `p = δ(I, 1, 2)` the zero measure also satisfies (2.4)–(2.5). -/
theorem section2_measure (p : Measure S) [IsProbabilityMeasure p] :
    Measurable g ∧
      IsProbabilityMeasure (gameMeasure p) ∧
      SatisfiesEquations p (gameMeasure p) ∧
      ∀ Q : Measure Game, IsProbabilityMeasure Q → SatisfiesEquations p Q → Q = gameMeasure p := by sorry

end RandomPIGame
