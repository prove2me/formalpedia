-- Prove2me | Theorems.Thm_PowerTwoChoices_Asymptotics_theorem_4
-- name    : PowerTwoChoices.Asymptotics.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:05.727328+00:00
-- url     : https://prove2.me/theorems/7114983a-27b8-45f2-baca-62da658ec22a
-- title:
--   Theorem 4 (limit clause): $T_d(\lambda)/\log T_1(\lambda)\to1/\log d$ as $\lambda\to1^-$
-- statement:
--   The paper states:
--
--   > **Theorem 4.** For $\lambda\in[0,1]$ and $d\ge2$, $T_d(\lambda)\le c_d(\log T_1(\lambda))$ for some constant $c_d$ dependent only on $d$. Furthermore,
--   > $$\lim_{\lambda\to1^-}\frac{T_d(\lambda)}{\log T_1(\lambda)}=\frac{1}{\log d}.$$
--
--   Here $T_d(\lambda)=\sum_{i\ge1}\lambda^{(d^i-d)/(d-1)}$ is the equilibrium expected time a customer spends in the limiting supermarket system when each customer joins the shortest of $d$ randomly sampled queues, and $T_1(\lambda)=1/(1-\lambda)$ is the expected time with one choice (an M/M/1 queue). This item formalizes the second ("Furthermore") clause: for every integer $d\ge2$,
--   $$\lim_{\lambda\to1^-}\frac{T_d(\lambda)}{\log T_1(\lambda)}=\frac{1}{\log d}.$$
--
--   So in heavy traffic, two or more choices reduce the expected time from $\frac1{1-\lambda}$ to about $\log_d\frac1{1-\lambda}$: an exponential improvement over one choice.
--
--   **Formalization Note.** Only the limit clause is formalized. The first clause is false as printed: $T_d(\lambda)\ge1$ for every $\lambda\in[0,1)$ (its first term is $\lambda^0=1$), while $\log T_1(\lambda)\to0$ as $\lambda\to0^+$, so no constant $c_d$ works near $\lambda=0$; the paper does not prove it ("We prove only the limiting statement"). Logarithms are natural; the limit is taken along $\lambda<1$ (`𝓝[<] 1`), where all quantities are finite and the series converge.
-- source:
--   Mitzenmacher, The Power of Two Choices in Randomized Load Balancing, IEEE Trans. Parallel Distrib. Syst. 12(10), 2001, p. 1099, Theorem 4 (second clause)

import Mathlib
import Definitions.Def_PowerTwoChoices_Asymptotics_ExpectedTime

open Filter Topology

namespace PowerTwoChoices.Asymptotics

/-- Theorem 4, limit clause (Mitzenmacher 2001, p. 1099): for every integer `d ≥ 2`,
`T_d(λ) / log T_1(λ) → 1 / log d` as `λ → 1⁻`. -/
theorem theorem_4 (d : ℕ) (hd : 2 ≤ d) :
    Tendsto (fun lam : ℝ => Td d lam / Real.log (T1 lam)) (𝓝[<] (1 : ℝ))
      (𝓝 (1 / Real.log (d : ℝ))) := by sorry

end PowerTwoChoices.Asymptotics
