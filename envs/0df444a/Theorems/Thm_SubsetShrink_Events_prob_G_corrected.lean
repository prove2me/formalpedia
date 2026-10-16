-- Prove2me | Theorems.Thm_SubsetShrink_Events_prob_G_corrected
-- name    : SubsetShrink.Events.prob_G_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:31:30.889004+00:00
-- url     : https://prove2.me/theorems/ee53bbda-0dac-4c4f-8f65-23414897e20f
-- title:
--   Theorem 1 (𝓖_s part, corrected: 3 log(1/δ₀)), p. 13; B.1, pp. 38–39 — P(𝓖'_s) ≥ 1 − δ₀
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ have columns of unit Euclidean norm, let $\sigma>0$, $1\le s\le p$ and $\delta_0\in(0,1]$, and let $\epsilon$ have independent $N(0,\sigma^2)$ coordinates. Then the event
--   $$\mathcal G'_s = \bigl\{\epsilon^\top X u \le \sigma\sqrt{5s\log(ep/s)+3\log(1/\delta_0)}\,\|Xu\|,\ \forall u\in B_0(s)\bigr\}$$
--   is measurable and
--   $$\mathbb P(\mathcal G'_s)\ge1-\delta_0 .$$
--
--   This is the fast-rate event of the paper's oracle inequalities, with the coefficient of $\log(1/\delta_0)$ corrected from $1$ to $3$.
--
--   **Formalization Note** The paper prints the event with $\log(1/\delta_0)$ instead of $3\log(1/\delta_0)$. As printed the bound is false: for $n=p=s=1$ and $X=[1]$ the printed event is $\{|\epsilon|\le\sigma\sqrt{5+L}\}$ with $L=\log(1/\delta_0)$, whose complement has probability $2\bar\Phi(\sqrt{5+L})$, and this exceeds $e^{-L}=\delta_0$ for $L\ge9$ (at $L=9$: $1.83\cdot10^{-4}>1.23\cdot10^{-4}$). The corrected constant $3$ follows from the argument the paper cites (Lemma 8 of its reference [51]): for a support $S$ of size $s$, $\sup_{\operatorname{supp}u\subseteq S}\epsilon^\top Xu/\|Xu\|$ is the norm of the projection of $\epsilon$ on the span of the columns in $S$, a $\sigma\chi$ variable with at most $s$ degrees of freedom; the Laurent–Massart bound $\mathbb P(\chi^2_s\ge s+2\sqrt{sx}+2x)\le e^{-x}$ with $x=s\log(ep/s)+\log(1/\delta_0)$, $2\sqrt{sx}\le s+x$ and $\log(ep/s)\ge1$ give the threshold $5s\log(ep/s)+3\log(1/\delta_0)$, and a union bound over $\binom ps\le(ep/s)^s$ supports gives failure probability at most $\delta_0$. The printed event is contained in the corrected one.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 13, Theorem 1 (P(G_s) ≥ 1 − δ0, event G_s on p. 13; constant corrected); proof B.1, pp. 38–39

import Mathlib
import Definitions.Def_SubsetShrink_Events_Model

open MeasureTheory ProbabilityTheory

namespace SubsetShrink.Events
theorem prob_G_corrected {n p s : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X)
    (σ : ℝ) (hσ : 0 < σ) (hs : 1 ≤ s) (hsp : s ≤ p) (δ0 : ℝ) (hδ0 : 0 < δ0) (hδ1 : δ0 ≤ 1) :
    MeasurableSet (Gc X σ δ0 s) ∧ 1 - δ0 ≤ (noiseLaw n σ (Gc X σ δ0 s)).toReal := by sorry
end SubsetShrink.Events
