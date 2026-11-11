-- Prove2me | Theorems.Thm_RAREPricing_Existence_lemma_3
-- name    : RAREPricing.Existence.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:25:49.295806+00:00
-- url     : https://prove2.me/theorems/c5f83de2-0387-40e1-87de-134aace4e3b1
-- title:
--   Lemma 3 — market shares can be restored on the upper boundary of a price-increase box
-- statement:
--   Fix a market and a setting with constants $\nu,\beta$, and let $A$ be a continuous allocation rule. Let $p\in\beta\Delta_m$, $M^+=\{j:p_j>0\}$, and let $z\in\mathbb R^m$ satisfy $z_j>p_j$ for $j\in M^+$ and $z_j=0$ for $j\notin M^+$. Then there is $q$ with
--   1. $p_j\le q_j\le z_j$ for all $j$;
--   2. $q_i=z_i$ for some $i\in M^+$;
--   3. $R_{\mathrm{all}}(q)\ge R_{\mathrm{all}}(p)=\nu\beta$;
--   4. for all $j\in[m]$,
--   $$\frac{R^A_j(q)}{R_{\mathrm{all}}(q)}=\frac{p_j}{\beta}=\frac{R^A_j(p)}{R_{\mathrm{all}}(p)}.$$
--   Here $R_{\mathrm{all}}(q)=\sum_jR^A_j(q)$.
--
--   This gives the covering condition for the KKM argument of Lemma 4.
--
--   Differences from the source:
--   - encoding: $z\in\prod_{j\in M^+}(p_j,\infty)\times\{0\}^{[m]\setminus M^+}$ → $0<p_j\Rightarrow p_j<z_j$ and $p_j=0\Rightarrow z_j=0$ for every $j$; reason: the same set, since $p\ge0$.
-- source:
--   Chaudhury, Garg, Huang, Sharma, RARE: Response-Aware Rational Equilibrium in Budget-Constrained Pricing Games, STOC 2027 submission (manuscript sha256 e9bb863f…), p. 18 (PDF 20), Lemma 3

import Mathlib
import Definitions.Def_RAREPricing_Existence_Model

namespace RAREPricing.Existence

theorem lemma_3 {n m : ℕ} (M : Market n m) (s : Setting)
    (A : (Fin m → ℝ) → (Fin n → Fin m → ℝ)) (hA : IsContinuousAllocationRule M s A)
    (p : Fin m → ℝ) (hp : p ∈ scaledSimplex m (beta M s))
    (z : Fin m → ℝ) (hz_pos : ∀ j, 0 < p j → p j < z j) (hz_zero : ∀ j, p j = 0 → z j = 0) :
    ∃ q : Fin m → ℝ,
      (∀ j, p j ≤ q j ∧ q j ≤ z j) ∧
      (∃ i, 0 < p i ∧ q i = z i) ∧
      (totalRevA A p ≤ totalRevA A q ∧ totalRevA A p = nu M s * beta M s) ∧
      (∀ j, revA A j q / totalRevA A q = p j / beta M s ∧
        p j / beta M s = revA A j p / totalRevA A p) := by sorry

end RAREPricing.Existence
