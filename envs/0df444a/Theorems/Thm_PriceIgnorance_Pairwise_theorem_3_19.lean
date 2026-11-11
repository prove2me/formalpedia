-- Prove2me | Theorems.Thm_PriceIgnorance_Pairwise_theorem_3_19
-- name    : PriceIgnorance.Pairwise.theorem_3_19
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:14:21.739557+00:00
-- url     : https://prove2.me/theorems/f43ea528-a72d-49f8-8c27-545069016198
-- title:
--   Theorem 3.19 — meta-theorem for random-order PoI, at prophet secretary: a finite-support bounded witness of random-order ratio $\le\alpha$ gives random-order $\mathrm{PoI}\le\alpha$
-- statement:
--   Consider the single-item prophet secretary problem: the values arrive in a uniformly random order, independent of the values, with identities revealed, and $\mathrm{OPT}(V)=\max_iV_i$. Let $\alpha\in\mathbb R$. Suppose $D$ is a joint distribution of nonnegative values on $\mathbb R^n$ such that
--
--   1. $D$ has finite support;
--   2. the coordinates are pairwise independent under $D$;
--   3. $\max_iV_i\le B$ almost surely, for some $B$;
--   4. $\mathbb E_D[\max_iV_i]>0$, and every random-order online algorithm $A$ satisfies $\mathbb E_D[\mathrm{val}(A,V)]\le\alpha\,\mathbb E_D[\max_iV_i]$, where $\mathrm{val}$ is averaged over the random order.
--
--   So $D$ witnesses that the optimal random-order pairwise-independent competitive ratio is at most $\alpha$. Then the random-order pairwise-independent price of ignorance satisfies
--   $$\mathrm{PoI}_{\mathrm{RO}}\le\alpha .$$
--
--   This is the inequality $\mathrm{PoI}\le\mathrm{CR}$ of Theorem 1.2 for prophet secretary.
--
--   Differences from the source:
--   - reading: Π admitting null-signal padding (not only in prefixes), for which an online algorithm knowing all values obtains OPT in any order → Π = the single-item prophet secretary problem with OPT(V) = max_i V_i; reason: Definition 3.14 is not precise mathematics; this is the instance Theorem 1.2 uses, and both conditions hold there (stop at the maximum)
--   - reading: witnessed by a finite-support, bounded value distribution → D pairwise independent, finitely supported, max_i V_i ≤ B a.s.; reason: the witness of the competitive ratio under pairwise independence is a pairwise-independent law, as in Theorem 3.16
--   - encoding: the optimal competitive ratio is at most α, as witnessed by D → ∀ A, E_D[val(A,V)] ≤ α · E_D[max_i V_i], together with 0 < E_D[max_i V_i]; reason: the witness's ratio sup_A E_D[val]/E_D[max] ≤ α is defined only when E_D[max] > 0 (footnote 3), and then it is this inequality
--   - encoding: finite-support joint distribution with OPT(V) ≤ B, nonnegative values → a probability measure on Fin n → ℝ carried by a finite set, with max_i V_i ≤ B and V_i ≥ 0 almost surely; reason: values of the prophet inequality are nonnegative (p. 1); OPT(V) = max_i V_i (p. 9)
--   - encoding: inf_A E_D[val(B,V)] / E_D[val(A,V)] (Definition 2.2) → E_D[val(B,V)] / sup_A E_D[val(A,V)]; reason: same value: the numerator is ≥ 0 and the sup is ≥ max_i E[V_i] > 0
--   - encoding: randomized online algorithms (mixtures of deterministic ones) → behavioural stopping probabilities p_i(history) ∈ [0,1], measurable in the history; reason: same value functions as mixtures of deterministic rules (Kuhn); measurability makes E_D[val] defined
--   - encoding: uniformly random order independent of the values, val averaged over it (p. 7) → σ uniform on permutations of Fin n, independent of values and internal randomness; identities revealed; val averaged over σ; reason: the standard prophet secretary model the paper uses
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 11, Theorem 3.19 (proof sketch p. 31); p. 9, Definitions 3.13–3.14

import Mathlib
import Definitions.Def_LaconicBarrier_KWiseIndep
import Definitions.Def_PriceIgnorance_Pairwise_Instance
import Definitions.Def_PriceIgnorance_Pairwise_Algorithms
import Definitions.Def_PriceIgnorance_Pairwise_Ratios

open MeasureTheory

namespace PriceIgnorance.Pairwise

/-- Theorem 3.19 (p. 11) for the prophet secretary problem: if a pairwise-independent joint
distribution `D` of nonnegative values with finite support and `max_i V_i ≤ B` witnesses that the
optimal random-order competitive ratio is at most `α` (every random-order online algorithm `A`
has `E_D[val(A, V)] ≤ α E_D[max_i V_i]`, `val` averaged over a uniformly random order), then the
random-order pairwise-independent price of ignorance is at most `α`. -/
theorem theorem_3_19 (α : ℝ) {n : ℕ} (D : Measure (Fin n → ℝ)) [IsProbabilityMeasure D]
    (hnonneg : ∀ᵐ v ∂D, ∀ i, 0 ≤ v i)
    (hfin : ∃ S : Finset (Fin n → ℝ), D (↑S)ᶜ = 0)
    (hpi : LaconicBarrier.KWiseIndep D coord 2)
    (B : ℝ) (hB : ∀ᵐ v ∂D, (⨆ i, v i) ≤ B)
    (hpos : 0 < expMax D)
    (hwit : ∀ A : OnlineAlgRO n, expVal randomOrder A D ≤ α * expMax D) :
    PoI randomOrder 2 ≤ α := by sorry

end PriceIgnorance.Pairwise
