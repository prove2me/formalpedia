-- Prove2me | Theorems.Thm_SumReLU_proposition_3_5
-- name    : SumReLU.proposition_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:35.100209+00:00
-- url     : https://prove2.me/theorems/0e20b10e-3b4a-4d34-8129-47f28d474cc4
-- title:
--   Proposition 3.5 — a CDR list for the localized distribution yields update directions with $|\hat r^{\perp v}\cdot\hat w_i^{\perp v}|\ge9/10$
-- statement:
--   Fix a unit vector $v\in\mathbb R^d$ and $\lambda\in(0,1)$, let $f(x)=\sum_i\beta_i\sigma(w_i\cdot x)$ be a Gaussian sum of $k$ ReLUs ($\beta_i\in[0,1]$, $\|w_i\|_2=1$), and put $\gamma=\lambda/100$. By Fact 3.4 the $(\gamma,v)$-rejection sampling distribution $D^{\gamma,v}$ is the Gaussian sum of ReLUs with coefficients $\tilde\beta_j$ and weights $\tilde w_j$. Let $L$ be any finite list of unit vectors that satisfies the guarantee of Assumption 1 for $D^{\gamma,v}$ at threshold $\lambda$:
--   $$
--   \text{for every } j \text{ with } \tilde\beta_j\ge\lambda \text{ there is } r\in L \text{ with } |r\cdot\tilde w_j|\ge0.99 .
--   $$
--   Then for every $i$ with $\beta_i\sin\theta_\pm(w_i,v)\ge\lambda$ there is $r\in L$ with $r^{\perp v}\ne0$ and
--   $$
--   \big|\widehat{r^{\perp v}}\cdot\widehat{w_i^{\perp v}}\big|\ge\frac{9}{10}.
--   $$
--
--   Since a procedure satisfying Assumption 1 returns such a list with probability at least $1-\delta$, this gives the paper's statement: with probability at least $1-\delta$ the list contains a near-ideal update direction for every component with $\beta_i\sin\theta_\pm(w_i,v)\ge\lambda$.
--
--   Differences from the source:
--   - generalization: CDR satisfying Assumption 1, run on samples of $D^{\gamma,v}$, returns a list $L$ such that with probability at least $1-\delta$ the conclusion holds → for every finite list $L$ of unit vectors satisfying Assumption 1's guarantee for $D^{\gamma,v}$, the conclusion holds; $\delta$ does not appear; reason: Assumption 1 gives such a list on an event of probability at least $1-\delta$, so the deterministic statement implies the printed one for every CDR
--   - encoding: $D^{\gamma,v}$ and its $\lambda$-heavy components → the parameters $(\tilde\beta_j,\tilde w_j)$ of Fact 3.4, heavy meaning $\tilde\beta_j\ge\lambda$; reason: by Fact 3.4 these are the coefficients and hidden vectors of $D^{\gamma,v}$
--   - encoding: $|\hat r_i^{\perp v}\cdot\hat w_i^{\perp v}|\ge9/10$ → $r^{\perp v}\ne0$ and the inequality with $\hat u=u/\|u\|_2$; reason: the normalization presupposes $r^{\perp v}\ne0$; asserting it rules out the junk value $\hat0=0$
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Proposition 3.5, p.14 (PDF p.16); Assumption 1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_SumReLU_reluSum
import Definitions.Def_SumReLU_thetaPM
import Definitions.Def_SumReLU_rejection

namespace SumReLU

/-- **Proposition 3.5** (Estimating Update Directions), deterministic form.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Proposition 3.5, p.14 (PDF p.16): "Fix a unit vector v ∈ ℝᵈ and let λ, δ ∈ (0, 1). Let D be a
Gaussian sum of k ReLUs and, given γ = λ/100, let D^{γ,v} be the (γ, v)-rejection sampling
distribution obtained from D. Then, procedure CDR(D^{γ,v}, λ, δ) that satisfies Assumption 1 applied
to i.i.d. samples from D^{γ,v} returns a list L such that with probability at least 1 − δ, for any
w_i with β_i sin(θ±(w_i, v)) ≥ λ, there exists a unit vector r_i ∈ L with |r̂_i^{⊥v} · ŵ_i^{⊥v}| ≥ 9/10."
Assumption 1, p.11 (PDF p.13): "… returns a list L ⊆ S^{d−1} … such that: for every λ-heavy
component i ∈ [k], there exists r_i ∈ L satisfying |r_i · w_i| ≥ 0.99."

**Formalization Note.** By Fact 3.4, `D^{γ,v}` is the Gaussian sum of `k` ReLUs with coefficients
`β̃_i` and weights `w̃_i`. Assumption 1's guarantee on CDR's success event is the hypothesis `hCDR`
on a finite list `L` of unit vectors (`λ`-heavy: `β̃_j ≥ λ`); the conclusion holds for every such
list, hence on CDR's success event, of probability at least `1 − δ`, for every CDR satisfying
Assumption 1. `δ` only names that failure probability and does not appear. The conclusion
asserts `r^{⊥v} ≠ 0`, so that `r̂^{⊥v}` is defined. -/
theorem proposition_3_5 {d k : ℕ} (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) (lam : ℝ)
    (hl0 : 0 < lam) (hl1 : lam < 1) (β : Fin k → ℝ) (w : Fin k → EuclideanSpace ℝ (Fin d))
    (hf : InClass β w) (L : Finset (EuclideanSpace ℝ (Fin d))) (hL : ∀ r ∈ L, ‖r‖ = 1)
    (hCDR : ∀ j, lam ≤ btilde (β j) (lam / 100) v (w j) →
      ∃ r ∈ L, (0.99 : ℝ) ≤ |inner ℝ r (wtilde (lam / 100) v (w j))|) :
    ∀ i, lam ≤ β i * Real.sin (thetaPM (w i) v) →
      ∃ r ∈ L, perp v r ≠ 0 ∧
        (9 / 10 : ℝ) ≤ |inner ℝ (normalize (perp v r)) (normalize (perp v (w i)))| := by sorry

end SumReLU
