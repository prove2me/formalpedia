-- Prove2me | Theorems.Thm_SwitchingStable_Universal_Supplement_lemma_20
-- name    : SwitchingStable.Universal.Supplement.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:38:17.55556+00:00
-- url     : https://prove2.me/theorems/a70c68a7-7551-406e-8b6b-bb5db8282ce2
-- title:
--   Lemma 20 — exactly central maximizers and both finite formulas
-- statement:
--   For $d\ge1$ and $0\le q<d$, let $f_{d,q}$ be the integrated capped-geometric logarithmic cost and $c_d=\max_q f_{d,q}$. Then
--
--   $$f_{d,q}=c_d\quad\Longleftrightarrow\quad q=\left\lfloor\frac{d-1}{2}\right\rfloor\ \text{or}\ q=\left\lceil\frac{d-1}{2}\right\rceil.$$
--
--   Thus there is one maximizing position for odd $d$ and two for even $d$. For every integer $m\ge1$,
--
--   $$c_{2m-1}=\sum_{k=2}^{m-1}\frac{2\log k}{(k+1)(k+2)}+\sum_{k=m}^{2m-2}\frac{4m\log k}{k(k+1)(k+2)}+\frac{\log(2m-1)}{2m-1},$$
--   $$c_{2m}=\sum_{k=2}^{m-1}\frac{2\log k}{(k+1)(k+2)}+\frac{3\log m}{(m+1)(m+2)}+\sum_{k=m+1}^{2m-1}\frac{2(2m+1)\log k}{k(k+1)(k+2)}+\frac{\log(2m)}{2m}.$$
--
--   Empty sums are zero. In particular $c_1=0$ and $c_2=\log(2)/2$. The statement also asserts integrability of every positive-cap finite experiment. These exact constants give the finite-list evaluations of Theorem 3.
--
--   Differences from the source:
--   - encoding: floor and ceiling of (d−1)/2 and inclusive finite sums → natural divisions (d−1)/2 and d/2, with finiteCost defined by the capped experiment; reason: these are the same one or two positions, including d=1 and m=1
--   - encoding: expectation of a bounded capped geometric logarithm → finite capped masses and explicit integrability conclusion; reason: retains the endpoint limit and prevents a nonintegrable integral default
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 36, PDF p. 37, Lemma 20; Section 6 and Appendices G–I

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Supplement_Costs

namespace SwitchingStable.Universal.Supplement

theorem lemma_20 :
    (∀ d q : ℕ, 1 ≤ d → q < d →
      (f d q = finiteCost d ↔ q = (d - 1) / 2 ∨ q = d / 2)) ∧
    (∀ m : ℕ, 1 ≤ m → finiteCost (2 * m - 1) = oddFormula m ∧
      finiteCost (2 * m) = evenFormula m) ∧
    (∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      MeasureTheory.Integrable (cappedLog a b) unitLaw) := by sorry

end SwitchingStable.Universal.Supplement
