-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_lemma_5
-- name    : RandomSizeStable.Stability.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:53.568672+00:00
-- url     : https://prove2.me/theorems/0a0a1416-355c-4dfd-b070-6a741e9cf60e
-- title:
--   Lemma 5 — rank-cut criterion and approximate stability (4.4)
-- statement:
--   Let $D$ be any positive-integer draw law, $C_0\ge0$, and $b\in[0,1]$ with $\phi_D(b)\le\mu_D$. Let $\lambda:[0,1]\to\mathbb R_{\ge0}$ satisfy $\lambda(0)=\lambda(1)=0$. Suppose nine closed intervals $J_0,\ldots,J_8\subseteq[0,b]$ cover $[0,b]$, and nine finite nonnegative Borel measures $\nu_j$ on $[0,1]$ each have mass $C_0$. Let $\tau_j:[0,1]\to\mathbb R_{\ge0}$ satisfy $\tau_j(0)=0$. For every $j$, $r\in J_j\cup[b,1]$, and $0\le a\le\min(p,r)$, $p\le A\le1$, assume
--   $$a+\lambda(p)\bigl(\Phi_D(a)+\Phi_D(A)-\Phi_D(a+A-p)-p\mu_D\bigr)
--   +\tau_j(p)(\mu_D-\phi_D(r))
--   \le\nu_j\{z:a\le\min(z,r)<A\}.$$
--   Then every stable lottery on every finite nonempty profile has distortion at most $1+2C_0$.
--
--   More generally, if $(1-p)\lambda(p)+\tau_0(p)\le B$ for every $p\in[0,1]$, then every $\delta\ge0$, every lottery $P$ with all $L_c(P)\le\mu_D+\delta$, every consistent pseudometric $d$, and every socially optimal $o$ satisfy
--   $$\operatorname{SC}_d(P)\le(1+2C_0)\operatorname{SC}_d(o)+B\delta\max_{c\in C}d(o,c).$$
--   No continuity, measurability or boundedness is imposed on $\lambda,\tau_j$. The measures may have atoms or continuous parts. The capped cut is half open exactly as displayed, including when $r=A$.
--
--   This criterion bounds actual costs using analytic witnesses; it is not assumed in the headline goal.
--
--   Differences from the source:
--   - encoding: finite nonempty voter and candidate sets with strict rankings → finite nonempty types and Election strict total orders; reason: these represent exactly the finite profiles in Section 2, with uniform voter averaging
--   - encoding: a positive-integer-valued random variable D → a PMF on the positive integers; reason: only the law enters these claims; countably infinite support and infinite mean remain allowed
--   - encoding: functions defined on [0,1] and nine closed intervals → total real functions constrained on [0,1], and intervals Icc(lo j,hi j) indexed by Fin 9; reason: all evaluations lie on the stated domain; closed intervals including degenerate or empty ones are representable
--   - encoding: finite Borel measures on [0,1] and their cut masses → Borel measures on the real line supported on [0,1], total mass ofReal C₀, and toReal cut masses; reason: extension by zero gives exactly the same measures; finite mass makes every conversion finite
--   - encoding: metric distortion at most 1+2C₀ → expected cost at most (1+2C₀) times each candidate cost for every consistent pseudometric; reason: C₀ is nonnegative, so the bound is at least one; this preserves the zero-optimum ratio convention
-- source:
--   Nisarg Shah, Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission #1342 (October 2026), p. 13, Lemma 5, Equation (4.4).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankBlocks

set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion

namespace RandomSizeStable.Stability

/-- Lemma 5, p.13: the nine-measure rank-cut criterion and its full
approximate-stability clause. Witnesses are hypotheses here, never in the goal. -/
theorem lemma_5 (D : PMF ℕ+) (C₀ b : ℝ) (hC : 0 ≤ C₀)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hphi : pgf D b ≤ benchmark D)
    (lam : ℝ → ℝ) (hlam : ∀ p ∈ Set.Icc (0 : ℝ) 1, 0 ≤ lam p)
    (hlam0 : lam 0 = 0) (hlam1 : lam 1 = 0)
    (lo hi : Fin 9 → ℝ)
    (hJ : ∀ j, Set.Icc (lo j) (hi j) ⊆ Set.Icc 0 b)
    (hcover : ∀ r ∈ Set.Icc (0 : ℝ) b, ∃ j, r ∈ Set.Icc (lo j) (hi j))
    (nu : Fin 9 → Measure ℝ)
    (hsupport : ∀ j, nu j ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hmass : ∀ j, nu j Set.univ = ENNReal.ofReal C₀)
    (tau : Fin 9 → ℝ → ℝ)
    (htau : ∀ j p, p ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ tau j p)
    (htau0 : ∀ j, tau j 0 = 0)
    (hcut : ∀ (j : Fin 9) (r : ℝ),
      r ∈ Set.Icc (lo j) (hi j) ∪ Set.Icc b 1 →
      ∀ a p A : ℝ, 0 ≤ a → a ≤ min p r → p ≤ A → A ≤ 1 →
        a + lam p * (primitive D a + primitive D A - primitive D (a + A - p)
          - p * benchmark D) + tau j p * (benchmark D - pgf D r) ≤
        (nu j {z : ℝ | a ≤ min z r ∧ min z r < A}).toReal) :
    ∀ (V C : Type) [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
      (E : Election V C),
      (∀ P : C → ℝ, IsStable D E P → HasDistortionAtMost E P (1 + 2 * C₀)) ∧
      (∀ B : ℝ, (∀ p ∈ Set.Icc (0 : ℝ) 1, (1 - p) * lam p + tau 0 p ≤ B) →
        ∀ (δ : ℝ), 0 ≤ δ → ∀ P : C → ℝ, IsApproximatelyStable D E P δ →
        ∀ d : V ⊕ C → V ⊕ C → ℝ, IsPseudometric d → Consistent E d →
        ∀ o : C, (∀ c, candCost d o ≤ candCost d c) →
          lotteryCost d P ≤ (1 + 2 * C₀) * candCost d o + B * δ * maxDistance d o) := by sorry

end RandomSizeStable.Stability
