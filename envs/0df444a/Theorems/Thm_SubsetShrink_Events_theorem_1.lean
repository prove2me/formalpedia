-- Prove2me | Theorems.Thm_SubsetShrink_Events_theorem_1
-- name    : SubsetShrink.Events.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T19:31:30.516804+00:00
-- url     : https://prove2.me/theorems/db2d6848-0522-46e1-80aa-2ff1fcdf952a
-- title:
--   Theorem 1, p. 13 — the events 𝓔_s, 𝓕, 𝓖_s, 𝓗 hold with probability ≥ 1 − s/(4ep), 1 − δ₀/2, 1 − δ₀, 1 − δ₀ (𝓖_s part corrected)
-- statement:
--   Consider the model $y=f^*+\epsilon$ with a deterministic design $X\in\mathbb R^{n\times p}$ whose columns have unit Euclidean norm and noise $\epsilon$ with independent $N(0,\sigma^2)$ coordinates, $\sigma>0$. Let $s\in[p]$ (that is, $1\le s\le p$) and $\delta_0\in(0,1]$. Then the four events $\mathcal E_s$, $\mathcal F$, $\mathcal G'_s$, $\mathcal H$ of p. 13 are measurable and
--   $$\mathbb P(\mathcal E_s)\ge1-\frac{s}{4ep},\qquad\mathbb P(\mathcal F)\ge1-\frac{\delta_0}{2},\qquad\mathbb P(\mathcal G'_s)\ge1-\delta_0,\qquad\mathbb P(\mathcal H)\ge1-\delta_0,$$
--   where
--   $$\mathcal E_s=\bigl\{\epsilon^\top Xu\le[4+\sqrt2]\sigma\sqrt{s\log(2ep/s)}\|u\|,\ \forall u\in B_0(s)\bigr\},$$
--   $$\mathcal F=\Bigl\{\epsilon^\top Xu\le[4+\sqrt2]\sigma\max\Bigl(\sum_{j=1}^pu^\sharp_j\sqrt{\log(2p/j)},\ \sqrt{\log(1/\delta_0)}\|Xu\|\Bigr),\ \forall u\in\mathbb R^p\Bigr\},$$
--   $$\mathcal G'_s=\bigl\{\epsilon^\top Xu\le\sigma\sqrt{5s\log(ep/s)+3\log(1/\delta_0)}\|Xu\|,\ \forall u\in B_0(s)\bigr\},$$
--   $$\mathcal H=\bigl\{\|X^\top\epsilon\|_\infty\le\sigma\sqrt{2\log(2p)}+\sigma\sqrt{2\log(1/\delta_0)}\bigr\}.$$
--
--   All oracle inequalities of the paper (Theorems 2–5) are deterministic statements on these events; this theorem converts them into high-probability and expected-error bounds.
--
--   **Formalization Note** The paper prints the third event as $\mathcal G_s$ with $\log(1/\delta_0)$ in place of $3\log(1/\delta_0)$ and claims $\mathbb P(\mathcal G_s)\ge1-\delta_0$. That claim is false: for $n=p=s=1$, $X=[1]$, $\mathbb P(\mathcal G_s^c)=2\bar\Phi(\sqrt{5+L})>e^{-L}=\delta_0$ whenever $L=\log(1/\delta_0)\ge9$. The statement here uses the corrected event; the correction follows from the Laurent–Massart $\chi^2$ tail bound with $x=s\log(ep/s)+\log(1/\delta_0)$ and a union bound over the $\binom ps\le(ep/s)^s$ supports (see `prob_G_corrected`). The probability space is $\mathbb R^n$ with the law $N(0,\sigma^2)^{\otimes n}$ of $\epsilon$; events are sets of noise vectors, and their measurability is part of the conclusion. The sorted sum $\sum_j u^\sharp_j\sqrt{\log(2p/j)}$ is encoded as a maximum over permutations (rearrangement inequality). The $\mathcal E_s$ bound has no free $\delta_0$: the paper derives it from $\mathcal F$ at $\delta_0=s/(2ep)$.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 13, Theorem 1 (G_s part corrected); proof B.1, pp. 38–39

import Mathlib
import Definitions.Def_SubsetShrink_Events_Model

open MeasureTheory ProbabilityTheory

namespace SubsetShrink.Events
theorem theorem_1 {n p s : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X)
    (σ : ℝ) (hσ : 0 < σ) (hs : 1 ≤ s) (hsp : s ≤ p) (δ0 : ℝ) (hδ0 : 0 < δ0) (hδ1 : δ0 ≤ 1) :
    (MeasurableSet (E X σ s) ∧
        1 - (s : ℝ) / (4 * Real.exp 1 * p) ≤ (noiseLaw n σ (E X σ s)).toReal) ∧
      (MeasurableSet (F X σ δ0) ∧ 1 - δ0 / 2 ≤ (noiseLaw n σ (F X σ δ0)).toReal) ∧
      (MeasurableSet (Gc X σ δ0 s) ∧ 1 - δ0 ≤ (noiseLaw n σ (Gc X σ δ0 s)).toReal) ∧
      (MeasurableSet (H X σ δ0) ∧ 1 - δ0 ≤ (noiseLaw n σ (H X σ δ0)).toReal) := by sorry
end SubsetShrink.Events
