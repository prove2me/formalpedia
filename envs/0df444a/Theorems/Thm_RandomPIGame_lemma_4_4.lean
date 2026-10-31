-- Prove2me | Theorems.Thm_RandomPIGame_lemma_4_4
-- name    : RandomPIGame.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:50.779+00:00
-- url     : https://prove2.me/theorems/0060ffe6-4be0-45dd-a691-36fecc2bc838
-- title:
--   Lemma 4.4: $(\omega_t)(\ell)=(\omega(\ell))_{t-1}$, and the subgames' truncated values are conditionally i.i.d. copies of $v_{t-1}$
-- statement:
--   Let $t\in\mathbb N_+$, and let $\mathbb P=\mathbb P_p$.
--
--   1. It holds that $(\omega_t)(\ell)=(\omega(\ell))_{t-1}$ for $\omega\in\Omega$ and each $\ell\in\{1,\dots,\xi_\omega(\oslash)\}$.
--   2. Take $(i,k,n)\in S$ such that $p_i(k,n)>0$. For $\ell\in\{1,\dots,n\}$ let $v_t(\ell):E(i,k,n)\to\mathbb R$ be the random variable $\omega\mapsto v_{(\omega_t)(\ell)}$. Under the conditional measure $\mathbb P(\cdot\mid E(i,k,n))$, the random variables $v_t(1),\dots,v_t(n)$ are independent, and each is distributed like the random variable $v_{t-1}$.
--
--   This is the first-step decomposition of the truncated value at the root.
--
--   Differences from the source:
--   - encoding: indices j, ℓ ∈ {1, …, n} → an index j : Fin n standing for j + 1; reason: a reindexing; no instance changes
--   - encoding: v_t(ℓ) is defined on E(i, k, n) → a total map on Ω through Game.child; reason: it agrees with the paper on E(i, k, n), which carries the conditional measure; for t ≥ 1 and ℓ ≤ n the node (ℓ) lies in the tree of ω_t
--   - encoding: a play is a finite or infinite sequence of nodes, and the payoff is the infimum of its capacities → a play is a sequence indexed by ℕ that stays at an end node once reached, and the payoff is the infimum over all stages; reason: stuttering does not change the set of capacities visited
--   - encoding: v_ω is the common value of sup inf and inf sup → value is defined as the sup inf; reason: the equality with inf sup is the milestone section2_value; the strategy types are nonempty and payoffs lie in [0, γ(⊘)], so both real extrema are genuine
--   - encoding: capacities and thresholds k in [0, ∞) → capacities and thresholds k in ℝ≥0; reason: Lean convention; the same numbers
--   - encoding: P_p is the Borel measure on Ω characterized by (2.4)–(2.5) → gameMeasure p is the pushforward of Measure.infinitePi under g; reason: this is the paper's own construction on p.8; the milestone section2_measure proves g measurable and identifies the two
--   - encoding: probabilities P(·) → Measure.real, a real number; reason: all measures involved are finite, so nothing is lost
-- source:
--   Flesch, Predtetchinski & Suomala, Random perfect information games, arXiv:2104.10528v1, Lemma 4.4, p.15

import Mathlib
import Definitions.Def_RandomPIGame_Primitive
import Definitions.Def_RandomPIGame_Game
import Definitions.Def_RandomPIGame_Measure
import Definitions.Def_RandomPIGame_Value

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RandomPIGame

/-- Subgames of truncated games. arXiv:2104.10528v1, Lemma 4.4, p.15. Let `t ∈ ℕ₊`.

1. `(ω_t)(ℓ) = (ω(ℓ))_{t-1}` for `ω ∈ Ω` and each `ℓ ∈ {1, …, ξ_ω(⊘)}`.
2. Take `(i, k, n) ∈ S` with `p_i(k, n) > 0`. Under `P(· | E(i, k, n))`, the random variables
   `v_t(ℓ) : ω ↦ v_{(ω_t)(ℓ)}`, `ℓ ∈ {1, …, n}`, are independent, and each is distributed like
   `v_{t-1} : ω ↦ v_{ω_{t-1}}`.

**Formalization Note.** The index `j : Fin n` stands for `ℓ = j + 1`. The paper defines `v_t(ℓ)` on
`E(i, k, n)`; the total map used here agrees with it there, and the conditional measure is carried
by `E(i, k, n)`. -/
theorem lemma_4_4 (p : Measure S) [IsProbabilityMeasure p] (t : ℕ) (ht : 1 ≤ t) :
    (∀ (ω : Game) (ℓ : ℕ+), (ℓ : ℕ) ≤ ω.ξ ω.root →
      (ω.trunc t).child ℓ = (ω.child ℓ).trunc (t - 1)) ∧
      ∀ (i : Player) (k : ℝ≥0) (n : ℕ), 0 < pMass p i k n →
        iIndepFun (fun (j : Fin n) (ω : Game) => ((ω.trunc t).child j.val.succPNat).value)
            ((gameMeasure p)[|E i k n]) ∧
          ∀ j : Fin n,
            ((gameMeasure p)[|E i k n]).map
                (fun ω : Game => ((ω.trunc t).child j.val.succPNat).value) =
              (gameMeasure p).map (fun ω : Game => (ω.trunc (t - 1)).value) := by sorry

end RandomPIGame
