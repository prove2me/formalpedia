-- Prove2me | Theorems.Thm_PriceIgnorance_Pairwise_theorem_3_16
-- name    : PriceIgnorance.Pairwise.theorem_3_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:14:36.44956+00:00
-- url     : https://prove2.me/theorems/719d8dd9-3c6e-4bbe-a2b1-070cd2787db2
-- title:
--   Theorem 3.16 — meta-theorem for PoI, at the prophet inequality: a finite-support bounded witness of competitive ratio $\le\alpha$ gives $\mathrm{PoI}\le\alpha$
-- statement:
--   Consider the single-item prophet inequality, with values arriving in the fixed order $V_1,\dots,V_n$ and offline optimum $\mathrm{OPT}(V)=\max_iV_i$. Let $\alpha\in\mathbb R$. Suppose $D$ is a joint distribution of nonnegative values on $\mathbb R^n$ such that
--
--   1. $D$ has finite support;
--   2. the coordinates are pairwise independent under $D$;
--   3. $\max_iV_i\le B$ almost surely, for some $B$;
--   4. $\mathbb E_D[\max_iV_i]>0$, and every online algorithm $A$ satisfies $\mathbb E_D[\mathrm{val}(A,V)]\le\alpha\,\mathbb E_D[\max_iV_i]$.
--
--   So $D$ witnesses that the optimal pairwise-independent competitive ratio is at most $\alpha$. Then the pairwise-independent price of ignorance (Definition 2.2) satisfies
--   $$\mathrm{PoI}\le\alpha .$$
--
--   This is the inequality $\mathrm{PoI}\le\mathrm{CR}$ of Theorem 1.2, once Lemma C.1 supplies finite-support bounded witnesses of every competitive ratio above $\mathrm{CR}$.
--
--   Differences from the source:
--   - reading: Π a finite-horizon stochastic online optimization problem admitting null-signal padding (Definitions 3.13, 3.14) → Π = the single-item prophet inequality with OPT(V) = max_i V_i; reason: Definition 3.14's clause 'may increase val by an arbitrarily small amount' is not precise mathematics; this is the instance Theorem 1.2 uses, and Remark 3.15 says it admits padding
--   - encoding: the optimal competitive ratio is at most α, as witnessed by D → ∀ A, E_D[val(A,V)] ≤ α · E_D[max_i V_i], together with 0 < E_D[max_i V_i]; reason: the witness's ratio sup_A E_D[val]/E_D[max] ≤ α is defined only when E_D[max] > 0 (footnote 3), and then it is this inequality
--   - encoding: finite-support joint distribution with OPT(V) ≤ B, nonnegative values → a probability measure on Fin n → ℝ carried by a finite set, with max_i V_i ≤ B and V_i ≥ 0 almost surely; reason: values of the prophet inequality are nonnegative (p. 1); OPT(V) = max_i V_i (p. 9)
--   - encoding: inf_A E_D[val(B,V)] / E_D[val(A,V)] (Definition 2.2) → E_D[val(B,V)] / sup_A E_D[val(A,V)]; reason: same value: the numerator is ≥ 0 and the sup is ≥ max_i E[V_i] > 0
--   - encoding: randomized online algorithms (mixtures of deterministic ones) → behavioural stopping probabilities p_i(history) ∈ [0,1], measurable in the history; reason: same value functions as mixtures of deterministic rules (Kuhn); measurability makes E_D[val] defined
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 10, Theorem 3.16 (proof pp. 10–11); p. 9, Definitions 3.13–3.14

import Mathlib
import Definitions.Def_LaconicBarrier_KWiseIndep
import Definitions.Def_PriceIgnorance_Pairwise_Instance
import Definitions.Def_PriceIgnorance_Pairwise_Algorithms
import Definitions.Def_PriceIgnorance_Pairwise_Ratios

open MeasureTheory

namespace PriceIgnorance.Pairwise

/-- Theorem 3.16 (p. 10) for the single-item prophet inequality: if a pairwise-independent joint
distribution `D` of nonnegative values with finite support and `max_i V_i ≤ B` witnesses that the
optimal competitive ratio is at most `α` (every online algorithm `A` has
`E_D[val(A, V)] ≤ α E_D[max_i V_i]`), then the pairwise-independent price of ignorance is at most
`α`. -/
theorem theorem_3_16 (α : ℝ) {n : ℕ} (D : Measure (Fin n → ℝ)) [IsProbabilityMeasure D]
    (hnonneg : ∀ᵐ v ∂D, ∀ i, 0 ≤ v i)
    (hfin : ∃ S : Finset (Fin n → ℝ), D (↑S)ᶜ = 0)
    (hpi : LaconicBarrier.KWiseIndep D coord 2)
    (B : ℝ) (hB : ∀ᵐ v ∂D, (⨆ i, v i) ≤ B)
    (hpos : 0 < expMax D)
    (hwit : ∀ A : OnlineAlg n, expVal fixedOrder A D ≤ α * expMax D) :
    PoI fixedOrder 2 ≤ α := by sorry

end PriceIgnorance.Pairwise
