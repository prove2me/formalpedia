-- Prove2me | Theorems.Thm_RobustSPA_IID_proposition_A_3_phi
-- name    : RobustSPA.IID.proposition_A_3_phi
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T09:37:14.929986+00:00
-- url     : https://prove2.me/theorems/96a8e173-e833-4c99-8c77-2d0571f702d3
-- title:
--   Proposition A-3, p. App-2 (properties of Φ*_n) — series form, (ODE-Φ), Φ*_n(r*_n+) = 0 and Φ*_n(1) = 1
-- statement:
--   Fix $n\ge1$ and let $r=r^*_n\in(0,1/n)$ solve the $r^*$-equation
--   $$(1-r)^{n-1}+\log r+\sum_{k=1}^{n-1}\frac{(1-r)^k}{k}=0 .$$
--   Let $\Phi^*_n$ be the reserve CDF of Theorem 1, which on $(r,1]$ is
--   $$\Phi^*_n(v)=\Big(\frac{v}{v-r}\Big)^{n-1}\log\frac vr-\sum_{k=1}^{n-1}\frac1k\Big(\frac{v}{v-r}\Big)^{n-1-k},$$
--   with $\Phi^*_n=0$ on $(-\infty,r]$ and $\Phi^*_n=1$ on $(1,\infty)$. Then:
--
--   1. (series) for $v\in(r,1]$, $\displaystyle\Phi^*_n(v)=\sum_{k=n}^{\infty}\frac1k\Big(\frac{v-r}{v}\Big)^{k-(n-1)}$;
--   2. (ODE-$\Phi$) for $v\in(r,1)$, $\displaystyle(\Phi^*_n)'(v)=\frac1v-\frac{(n-1)r}{v(v-r)}\,\Phi^*_n(v)$;
--   3. $\Phi^*_n(v)\to0$ as $v\downarrow r$;
--   4. $\Phi^*_n(1)=1$.
--
--   These are the analytic properties of the optimal reserve distribution asserted in Proposition A-3. The proofs of Theorem 1 and Proposition 2 use them when they substitute (ODE-$\Phi$) into the regret expression (Regret-$\mathbf F$).
--
--   **Formalization Note.** This is the part of `RobustSPA.IID.proposition_A_3` that concerns $\Phi^*_n$ alone. The statement is copied verbatim from the second conjunct of that theorem, leaving out the existence and uniqueness of $r^*_n$ and the value of the regret at $\mathbf F^*_n$. The series is indexed by $j=k-n\ge0$.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. App-2, Proposition A-3 (the statements about $\Phi^*_n$: its series representation, that it solves (ODE-$\Phi$), $\Phi^*_n(r^*_n)=0$ and $\Phi^*_n(1)=1$)

import Mathlib
import Definitions.Def_RobustSPA_IID_Setting

namespace RobustSPA.IID

open MeasureTheory

theorem proposition_A_3_phi (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / n))
    (hrEq : rEq n r = 0) :
    (∀ v ∈ Set.Ioc r 1, HasSum
        (fun j : ℕ => 1 / ((j + n : ℕ) : ℝ) * ((v - r) / v) ^ (j + 1)) (PhiStar n r v)) ∧
      (∀ v ∈ Set.Ioo r 1, HasDerivAt (PhiStar n r)
        (1 / v - ((n : ℝ) - 1) * r / (v * (v - r)) * PhiStar n r v) v) ∧
      Filter.Tendsto (PhiStar n r) (nhdsWithin r (Set.Ioi r)) (nhds 0) ∧
      PhiStar n r 1 = 1 := by sorry

end RobustSPA.IID
