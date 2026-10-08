-- Prove2me | Theorems.Thm_ProbMetricStab_MixedInt_lemma_3_5_a
-- name    : ProbMetricStab.MixedInt.lemma_3_5_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:13:02.456571+00:00
-- url     : https://prove2.me/theorems/26500ed9-fe96-49c4-90bd-f9600dce4e02
-- title:
--   Lemma 3.5 (i)–(ii), p. 15 — countable Borel partition of 𝒯 on whose pieces Φ is uniformly Lipschitz
-- statement:
--   Let $\Phi$ be the mixed-integer value function (10), with recourse data $q,\bar q,W,\bar W$ satisfying (B1) (rational $W$, $\bar W$) and (B3) (dual feasibility), and let $\mathcal T$ be its feasibility set. Then there is a countable partition of $\mathcal T$ into Borel sets,
--   $$
--   \mathcal T=\bigcup_{i\in\mathbb N}\mathcal B_i,
--   $$
--   such that
--
--   1. each piece has the form $\mathcal B_i=\{b_i+\operatorname{pos}\bar W\}\setminus\bigcup_{j=1}^{N_0}\{b_{ij}+\operatorname{pos}\bar W\}$ with $b_i,b_{ij}\in\mathbb R^r$ and one $N_0$ for all $i$;
--   2. there is $N_1\in\mathbb N$ such that for every $t\in\mathcal T$ the ball $\mathbb B(t,1)$ meets at most $N_1$ different pieces;
--   3. the restriction of $\Phi$ to each $\mathcal B_i$ is Lipschitz continuous with a constant $L_\Phi>0$ not depending on $i$.
--
--   This is the structural description of mixed-integer value functions with rational data that drives the stability analysis of §3.2: on each of countably many locally finite pieces, $\Phi$ behaves like the value function of a linear program.
--
--   **Formalization Note** The pieces are a family $(\mathcal B_i)_{i\in\mathbb N}$ of pairwise disjoint Borel sets (empty pieces are allowed). "At most $N_1$ different subsets" is stated as: every finite set of indices whose pieces meet the closed ball of radius 1 around $t$ has at most $N_1$ elements. The Lipschitz estimate compares real values of $\Phi$, which is finite on $\mathcal T$ under (B3). Condition (B2), which the lemma also assumes, concerns $h$, $T$, $\Xi$ and $X$ only and plays no role in a statement about $\Phi$, so it is omitted.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 15, Lemma 3.5 (i)–(ii)

import Mathlib
import Definitions.Def_ProbMetricStab_MixedInt_Setting
open MeasureTheory Matrix
open scoped ENNReal NNReal Pointwise

namespace ProbMetricStab.MixedInt
theorem lemma_3_5_a {r mh mb : ℕ} (R : Recourse r mh mb) (hB1 : R.B1) (hB3 : R.B3) :
    ∃ B : ℕ → Set (EuclideanSpace ℝ (Fin r)),
      (∀ i, MeasurableSet (B i)) ∧ Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (⋃ i, B i) = R.Tset ∧
      (∃ (N₀ : ℕ) (b : ℕ → EuclideanSpace ℝ (Fin r)) (bb : ℕ → Fin N₀ → EuclideanSpace ℝ (Fin r)),
        ∀ i, B i = (b i +ᵥ R.posWb) \ ⋃ j, (bb i j +ᵥ R.posWb)) ∧
      (∃ N₁ : ℕ, ∀ t ∈ R.Tset, ∀ I : Finset ℕ,
        (∀ i ∈ I, (B i ∩ Metric.closedBall t 1).Nonempty) → I.card ≤ N₁) ∧
      (∃ LΦ : ℝ, 0 < LΦ ∧ ∀ i, ∀ t ∈ B i, ∀ t' ∈ B i,
        |(R.Phi t).toReal - (R.Phi t').toReal| ≤ LΦ * dist t t') := by sorry
end ProbMetricStab.MixedInt
