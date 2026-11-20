-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_rank_cut_certificate_dStar
-- name    : RandomSizeStable.Stability.rank_cut_certificate_dStar
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-19T17:00:03.164685+00:00
-- url     : https://prove2.me/theorems/0b312552-c973-4b33-a400-9e4386087c66
-- title:
--   Rank-cut certificate for the draw law of Figure 3 (Theorem 1's computer-checked step)
-- statement:
--   Let $D^\star$ be the draw law of Figure 3 (`dStar`: $\Pr[D^\star=1]=19/73$, $\Pr[D^\star=2]=35/146$, $\Pr[D^\star=32]=1/2$), with $\phi$ = `pgf dStar`, $\Phi$ = `primitive dStar`, $\mu$ = `benchmark dStar`, and $C_0=113609/200000$. There exist $b\in[0,1]$ with $\phi(b)\le\mu$, a function $\lambda$ with $\lambda\ge0$ on $[0,1]$ and $\lambda(0)=\lambda(1)=0$, closed intervals $[\mathrm{lo}_j,\mathrm{hi}_j]\subseteq[0,b]$ ($j<9$) covering $[0,b]$, Borel measures $\nu_j$ on $\mathbb R$ carried by $[0,1]$ and of total mass $C_0$, and functions $\tau_j\ge0$ on $[0,1]$ with $\tau_j(0)=0$, such that for every $j$, every $r\in[\mathrm{lo}_j,\mathrm{hi}_j]\cup[b,1]$ and all $0\le a\le\min(p,r)$, $p\le A\le1$:
--   $$a+\lambda(p)\bigl(\Phi(a)+\Phi(A)-\Phi(a+A-p)-p\mu\bigr)+\tau_j(p)\bigl(\mu-\phi(r)\bigr)\le\nu_j\bigl(\{z: a\le\min(z,r)<A\}\bigr).$$
--
--   These are exactly the hypotheses of the rank-cut criterion (Lemma 5, p. 13) at $D=D^\star$, $C_0=113609/200000$. The paper proves Theorem 1 by exhibiting the witnesses in the coefficient table `rank-cut-witness.json` of its repository (`b` = 2840189/5000000, nine cutoffs $h_j$, atoms and densities of the $\nu_j$) and verifying the displayed inequality by exact rational interval arithmetic (Section 5, Appendix A). This statement is the existence of that certificate; with `RandomSizeStable.Stability.lemma_5` and `RandomSizeStable.Stability.theorem_3` it gives Theorem 1.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), p. 14-16, 24, Theorem 1, proof: the rank-cut certificate for the draw law of Figure 3.

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_DrawLaw

set_option autoImplicit false

open MeasureTheory RandomSizeStable.Stability

theorem RandomSizeStable.Stability.rank_cut_certificate_dStar :
    ∃ (b : ℝ) (lam : ℝ → ℝ) (lo hi : Fin 9 → ℝ) (nu : Fin 9 → Measure ℝ)
      (tau : Fin 9 → ℝ → ℝ),
      (0 ≤ (113609 / 200000 : ℝ)) ∧
      (b ∈ Set.Icc (0 : ℝ) 1) ∧ (pgf dStar b ≤ benchmark dStar) ∧
      (∀ p ∈ Set.Icc (0 : ℝ) 1, 0 ≤ lam p) ∧
      (lam 0 = 0) ∧ (lam 1 = 0) ∧
      (∀ j, Set.Icc (lo j) (hi j) ⊆ Set.Icc 0 b) ∧
      (∀ r ∈ Set.Icc (0 : ℝ) b, ∃ j, r ∈ Set.Icc (lo j) (hi j)) ∧
      (∀ j, nu j ((Set.Icc (0 : ℝ) 1)ᶜ) = 0) ∧
      (∀ j, nu j Set.univ = ENNReal.ofReal (113609 / 200000 : ℝ)) ∧
      (∀ j p, p ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ tau j p) ∧
      (∀ j, tau j 0 = 0) ∧
      (∀ (j : Fin 9) (r : ℝ),
        r ∈ Set.Icc (lo j) (hi j) ∪ Set.Icc b 1 →
        ∀ a p A : ℝ, 0 ≤ a → a ≤ min p r → p ≤ A → A ≤ 1 →
          a + lam p * (primitive dStar a + primitive dStar A - primitive dStar (a + A - p)
            - p * benchmark dStar) + tau j p * (benchmark dStar - pgf dStar r) ≤
          (nu j {z : ℝ | a ≤ min z r ∧ min z r < A}).toReal) := by sorry
