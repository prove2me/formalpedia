-- Prove2me | Theorems.Thm_Plasticity_Ext_KMRate_binomial_bound
-- name    : Plasticity.Ext.KMRate.binomial_bound
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T17:55:17.73078+00:00
-- url     : https://prove2.me/theorems/90326ea3-c933-4956-813e-912a31cf78b2
-- title:
--   The Krasnoselskii–Mann residual is bounded by a binomial average of ballot probabilities
-- statement:
--   Let $C$, $D$, $K$, $\alpha$ and $P=(1-\alpha)I+\alpha K$ be as in the card `Plasticity.Ext.KMRate`, and put $u=2\alpha(1-\alpha)$. Then for every $x\in C$ and every $n\ge0$,
--   $$\bigl\|P^n(x)-K(P^n(x))\bigr\|\le D\sum_{m=0}^{n}\binom nm u^m(1-u)^{n-m}\,\frac{\binom{m}{\lfloor m/2\rfloor}}{2^m}.$$
--   Here $\binom{m}{\lfloor m/2\rfloor}2^{-m}$ is the probability that a simple random walk started at $0$ stays nonnegative for $m$ steps, so the right side is $D\,\mathbb E\bigl[F(M)\bigr]$ for $M\sim\mathrm{Bin}(n,u)$ and $F(m)=\binom{m}{\lfloor m/2\rfloor}2^{-m}$.
-- source:
--   R. Cominetti, J. A. Soto and J. Vaisman, Israel J. Math. 199 (2014), 757–772 (arXiv:1206.4195): Corollary 3 with the bound ‖x_n−Tx_n‖ ≤ c_{n,n+1}/α_{n+1} = Pⁿ below it, and Propositions 4–5, for α_i ≡ α and diam(C) ≤ D

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.Ext.KMRate
theorem binomial_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hconv : Convex ℝ C) (D : ℝ) (hD : ∀ x ∈ C, ∀ y ∈ C, ‖x - y‖ ≤ D)
    (K : E → E) (hmaps : Set.MapsTo K C C) (hlip : LipschitzOnWith 1 K C)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) (x : E) (hx : x ∈ C) :
    ‖(fun z => (1 - α) • z + α • K z)^[n] x - K ((fun z => (1 - α) • z + α • K z)^[n] x)‖
      ≤ D * ∑ m ∈ Finset.range (n + 1),
          (n.choose m : ℝ) * (2 * α * (1 - α)) ^ m * (1 - 2 * α * (1 - α)) ^ (n - m) *
            ((m.choose (m / 2) : ℝ) / 2 ^ m) := by sorry
end Plasticity.Ext.KMRate
