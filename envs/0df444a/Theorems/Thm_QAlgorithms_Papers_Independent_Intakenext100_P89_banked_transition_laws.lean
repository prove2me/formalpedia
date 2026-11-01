-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P89_banked_transition_laws
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P89.banked_transition_laws
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:29:05.885267+00:00
-- url     : https://prove2.me/theorems/caa7d9a3-d4b5-42be-94df-f44727e834fb
-- title:
--   Banked construction: three conditional binomial laws
-- statement:
--   Use the independent-loss device model with $\eta_s,\eta_d,\eta_c\in(0,1]$, $\alpha>0$, $\beta,\tau_s,\tau_f\ge0$, and positive propagation speeds in consistent units. Put $v=\eta_s\eta_d$, $h=v/(2-v)$, $a=e^{-\beta\tau_s c_{\rm ch}}$, $G=[v(2-v)]^3/32$ and
--
--   $$\mu_l=ha^{l+1},\qquad p_l=\mu_l^2\left(\frac{v^2}{2}+\frac{v^4}{4}\right).$$
--
--   For any nonnegative integral source count $N_s$, bank sizes $y,y_1,y_2$, count $x$, and fusion level $l\ge1$, independent trials give the following count laws:
--
--   $$\Pr[X_{\rm GHZ}=x]=B(x,\lfloor N_s/6\rfloor,G),\quad \Pr[X_{\rm early}=x\mid y]=B(x,y,ah),\quad \Pr[X_l=x\mid y_1,y_2]=B(x,\min\{y_1,y_2\},p_l).$$
--
--   Here $B(x,N,p)=\binom Nx p^x(1-p)^{N-x}$ for $0\le x\le N$ and is zero otherwise. The first experiment attempts one GHZ state per six sources, the second makes the specified early photon measurement on each of $y$ GHZ fragments, and the third pairs daughter copies and discards the unmatched excess. These are exact conditional transition laws, without an inferred global allocation or Monte Carlo success guarantee.
-- source:
--   Rate-distance tradeoff and resource costs for all-optical quantum repeaters, arXiv:1603.01353v4, PDF p. 8, III.A.2: GHZ, early-measurement and banked-fusion count laws

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P89

namespace QAlgorithms.Papers.Independent.Intakenext100.P89

open scoped BigOperators ComplexConjugate

-- Accepted probability primitives: symbol true is success; choose n x is zero for x > n.

open QAlgorithms.Papers.Independent.Information100.P54 (binomialMass)

open QAlgorithms.Papers.Independent.Information100.P56 (bernoulli)

noncomputable section

/-- Source pp.8--9, III.A.2: GHZ, early-measurement and conditional fusion count laws.
Given daughter counts, min(y1,y2) trials are performed and unmatched excess discarded.
This does not supply a global Monte Carlo allocation rule or ancilla resource budget. -/
theorem banked_transition_laws (d : Devices) (nSources y y1 y2 l x : ℕ) (hl : 0 < l) :
    countLaw (nSources / 6) (ghzSuccess d) x =
      binomialMass (nSources / 6) (ghzSuccess d) x ∧
    countLaw y (chipSurvival d * etaGHZ d) x =
      binomialMass y (chipSurvival d * etaGHZ d) x ∧
    countLaw (min y1 y2) (bankFusionSuccess d l) x =
      binomialMass (min y1 y2) (bankFusionSuccess d l) x := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P89
