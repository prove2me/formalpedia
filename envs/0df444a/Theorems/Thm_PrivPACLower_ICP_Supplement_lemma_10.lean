-- Prove2me | Theorems.Thm_PrivPACLower_ICP_Supplement_lemma_10
-- name    : PrivPACLower.ICP.Supplement.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:11:49.164953+00:00
-- url     : https://prove2.me/theorems/9818e5d0-5caf-46a0-b086-4fe709f31c8d
-- title:
--   Lemma 10 (used in the proof of Theorem 4) — pairwise-gap bound for privately comparable distributions
-- statement:
--   Let $\Omega$ be a finite set and $P_1,\dots,P_s$ probability distributions on $\Omega$ such that
--   $$P_i(E)\le e^{\varepsilon}P_1(E)+\delta\qquad\text{for every } i\in[s] \text{ and every } E\subseteq\Omega.$$
--   Let $v_1,\dots,v_s:\Omega\to[0,1]$. If for some $\Gamma>\delta$ we have $\mathbb E_{P_i}[v_j]-\mathbb E_{P_j}[v_i]\ge\Gamma$ for every $i<j$, then
--   $$s\le\exp\Bigl(1+\frac{\pi e^{\varepsilon/2}}{\Gamma-\delta}\Bigr).$$
--
--   This bounds how many outputs of a private algorithm can be pairwise separated, and replaces the composition of many outputs in the threshold lower bound of Theorem 4.
--
--   **Formalization Note** Distributions are given by nonnegative mass functions summing to one; $P_1$ is index $0$.
--
--   Differences from the source:
--   - encoding: distributions P_1, ..., P_s on a finite set and expectations → functions P : Fin s -> Omega -> R, nonnegative with total mass 1, and finite sums; reason: on a finite set a distribution is its mass function; index 0 is P_1
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 19, Lemma 10 (proof p. 44). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP.Supplement


theorem lemma_10 {Ω : Type*} [Fintype Ω] (s : ℕ) (P : Fin s → Ω → ℝ)
    (hPnn : ∀ i ω, 0 ≤ P i ω) (hPsum : ∀ i, ∑ ω, P i ω = 1) (ε δ Γ : ℝ)
    (hcomp : ∀ (i : Fin s) (E : Finset Ω),
      ∑ ω ∈ E, P i ω ≤ Real.exp ε * ∑ ω ∈ E, P ⟨0, i.pos⟩ ω + δ)
    (v : Fin s → Ω → ℝ) (hv : ∀ i ω, 0 ≤ v i ω ∧ v i ω ≤ 1) (hΓ : δ < Γ)
    (hgap : ∀ i j : Fin s, i < j → Γ ≤ ∑ ω, P i ω * v j ω - ∑ ω, P j ω * v i ω) :
    (s : ℝ) ≤ Real.exp (1 + Real.pi * Real.exp (ε / 2) / (Γ - δ)) := by sorry

end PrivPACLower.ICP.Supplement
