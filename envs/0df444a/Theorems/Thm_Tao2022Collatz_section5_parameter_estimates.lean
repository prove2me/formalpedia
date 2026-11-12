-- Prove2me | Theorems.Thm_Tao2022Collatz_section5_parameter_estimates
-- name    : Tao2022Collatz.section5_parameter_estimates
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-11T23:48:15.731337+00:00
-- url     : https://prove2.me/theorems/e229c118-0763-4229-b918-a024257d5294
-- title:
--   Parameter estimates for Tao's Section 5 (choices of $n_0$, $m_0$, $D$, $L$, $K$)
-- statement:
--   Let $n_0(x)=\lfloor\log x/(10\log2)\rfloor$ (Tao (5.1)), $D(x)=2\log^{3/5}x$, $L(x)=\log^{1/5}x$, $W=2(2D+1)\log2+\log\frac43$, $\widetilde W=W+D\log2+\log 2$, $\varepsilon=2(3/2)^{n_0}/x$, $m_0=\lceil(W+2(2D+1)\log2+1)/\log\frac43\rceil$, $K=\lceil 2n_0+D\rceil$, $D_m=\lceil4D+2\rceil$ (each given as any function satisfying its defining equation). Write $\log x=u^5$ with $u\ge1000$. Then a fixed list of elementary estimates holds, among them: $D=2u^3$, $L=u$, $6.931\,n_0\le\log x\le6.932(n_0+1)$, $0\le W\le6u^3$, $\widetilde W\le8u^3$, $u\le m_0\le52u^3$, $m_0\le n_0$, $\varepsilon u\le1$, $4\cdot3^{n_0+m_0}2^{D_m}\le x$, $\sqrt{n_0L}+L\le D$; for every $a\in[\alpha,\alpha^2]$ ($\alpha=1.001$) the window inequalities relating $\log x^a$, $n_0\log\frac34$, $m_0\log\frac43$ and $\widetilde W$ that place the first passage time in Tao's interval $I_y$; and the final error bookkeeping, e.g. $4\big(n_02^{-K}+C_{osc}m_0^{-1}+2n_0e^{-L/24}\big)\le4(1+C_{osc}+2\cdot137594142720)/u$ and $8x^{-1/20000}+2\log x\,e^{-\log^{1/5}x/24}\le(8+2\cdot137594142720)/u$ (the formal statement lists every inequality exactly).
--
--   Role: these are the numerical parameter estimates of Tao's Section 5 (the choices (5.1)-(5.2) and the "straightforward calculations" behind (5.3), (5.9)-(5.16) and the final error terms), isolated so that the probabilistic argument for Proposition 1.11 can use them as black boxes.
--
--   **Formalization Note**: the parameters are passed as arbitrary functions with their defining equations. Here $m_0$ is of size $\log^{3/5}x$ rather than Tao's $(\alpha-1)\log x/100$ in (5.2); any $m_0\to\infty$ with $3^{m_0}$ small suffices for the Section 5 argument and this choice keeps the error terms explicit.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7, Section 5: parameter choices (5.1)-(5.2) and the calculations behind (5.3), (5.9)-(5.16) in the proof of Proposition 1.11 assuming Proposition 1.14. https://arxiv.org/abs/1909.03562

import Mathlib
import Definitions.Def_syracuseStep

namespace Tao2022Collatz

theorem section5_parameter_estimates :
    ∀ (pn0 : ℝ → ℕ) (pD pL pW pWt peps : ℝ → ℝ) (pm0 pK pDm : ℝ → ℕ),
    (∀ x, pn0 x = ⌊Real.log x / (10 * Real.log 2)⌋₊) →
    (∀ x, pD x = 2 * Real.log x ^ ((3 : ℝ) / 5)) →
    (∀ x, pL x = Real.log x ^ ((1 : ℝ) / 5)) →
    (∀ x, pW x = 2 * ((2 * pD x + 1) * Real.log 2) + Real.log (4 / 3)) →
    (∀ x, pWt x = pW x + pD x * Real.log 2 + Real.log 2) →
    (∀ x, peps x = 2 * (3 / 2 : ℝ) ^ (pn0 x) / x) →
    (∀ x, pm0 x = ⌈(pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1) / Real.log (4 / 3)⌉₊) →
    (∀ x, pK x = ⌈2 * (pn0 x : ℝ) + pD x⌉₊) →
    (∀ x, pDm x = ⌈4 * pD x + 2⌉₊) →
    (∀ (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5),
      1 ≤ x ∧ 0 ≤ pD x ∧ pD x = 2 * u ^ 3 ∧ pL x = u ∧ 1000000 * u ^ 3 ≤ Real.log x ∧
    u ≤ u ^ 3 ∧ 6.931 * (pn0 x : ℝ) ≤ Real.log x ∧ Real.log x ≤ 6.932 * ((pn0 x : ℝ) + 1) ∧
    0 ≤ pW x ∧ pW x ≤ 6 * u ^ 3 ∧ 0 ≤ pWt x ∧ pWt x ≤ 8 * u ^ 3 ∧
    pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1 ≤ pm0 x * Real.log (4 / 3) ∧
    (pm0 x : ℝ) * Real.log (4 / 3) ≤ 13 * u ^ 3 ∧ (pm0 x : ℝ) ≤ 52 * u ^ 3 ∧ 1 ≤ pm0 x ∧
    u ≤ (pm0 x : ℝ) ∧ 2 * (pn0 x : ℝ) + pD x ≤ pK x ∧
    4 * pD x + 2 ≤ pDm x ∧ (pDm x : ℝ) ≤ 8 * u ^ 3 + 3) ∧
    (∀ (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5),
      0 ≤ peps x ∧ peps x * u ≤ 1 ∧ peps x ≤ 1 ∧ 2 * (3 / 2 : ℝ) ^ (pn0 x) ≤ peps x * x ∧
    4 * (3 : ℝ) ^ (pn0 x + pm0 x) * 2 ^ (pDm x) ≤ x ∧
    1 * (Real.sqrt (pn0 x * pL x) + pL x) ≤ pD x ∧ pm0 x ≤ pn0 x) ∧
    (∀ (x u a : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) (ha1 : 1001 / 1000 ≤ a) (ha2 : a ≤ 1002001 / 1000000),
      16 ≤ x ^ a ∧ x ≤ x ^ a ∧ x ^ a + 1 ≤ (x ^ a) ^ ((1001 : ℝ) / 1000) ∧ (4 : ℝ) ^ (pn0 x) ≤ x ^ a ∧
    ((1001 : ℝ) / 1000) * Real.log (x ^ a) + pn0 x * Real.log (3 / 4) + (2 * pD x + 1) * Real.log 2 ≤ Real.log x ∧
    (pm0 x + 1) * Real.log (4 / 3) + (2 * pD x + 1) * Real.log 2 ≤ Real.log (x ^ a) - Real.log x ∧
    2 * pm0 x * Real.log (4 / 3) ≤ Real.log (x ^ a) - Real.log x + pWt x ∧
    2 * pWt x ≤ Real.log (x ^ a) - Real.log x + pWt x ∧
    Real.log (x ^ a) - Real.log x + pWt x ≤ ((1001 : ℝ) / 1000) * Real.log (x ^ a) - Real.log x - pWt x ∧
    ((1001 : ℝ) / 1000) * Real.log (x ^ a) - Real.log x - pWt x ≤ pn0 x * Real.log (4 / 3) ∧
    4 ≤ (((1001 : ℝ) / 1000) - 1) * Real.log (x ^ a)) ∧
    (∀ (ε eb Wt Λ ly h u : ℝ) (hu : 1000 ≤ u) (hly : u ^ 5 / 1000 ≤ ly) (hε0 : 0 ≤ ε) (hεu : ε * u ≤ 1) (hε1 : ε ≤ 1) (heb : 0 ≤ eb) (hWt0 : 0 ≤ Wt) (hWt : Wt ≤ 8 * u ^ 3) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ 4) (ha : 1 / 4 ≤ h) (hb : h ≤ 1 / 3),
      (4 * (ε * (ly / h + 1) * 4 + (ly / h + 1) * eb + (1 + ε) * (2 * (2 * Wt / h + 1)) * 4) / ly +
      Λ * (4 * ((2 * Wt / h + 1) + 2 / h) / ly)) ≤ 5500 / u + 20 * eb) ∧
    (∀ (x u Cosc : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) (hCosc : 0 ≤ Cosc),
      4 * ((pn0 x : ℝ) * (1 / 2) ^ (pK x) + Cosc * (pm0 x : ℝ) ^ (-(1 : ℝ)) +
      2 * pn0 x * Real.exp (-(1 * pL x) / 24)) ≤ 4 * (1 + Cosc + 2 * 137594142720) / u) ∧
    (∀ (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5),
      8 * x ^ (-(1 / 20000 : ℝ)) + 2 * Real.log x * Real.exp (-(Real.log x ^ ((1 : ℝ) / 5)) / 24) ≤
      (8 + 2 * 137594142720) / u) := by sorry

end Tao2022Collatz
