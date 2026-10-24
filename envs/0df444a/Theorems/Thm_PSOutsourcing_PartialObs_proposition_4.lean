-- Prove2me | Theorems.Thm_PSOutsourcing_PartialObs_proposition_4
-- name    : PSOutsourcing.PartialObs.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:09.000617+00:00
-- url     : https://prove2.me/theorems/c43dbbb9-9325-4d6c-9d6a-86d3f197f011
-- title:
--   Proposition 4, p. 20 — the value of outsourcing is affected only by upward belief drift, strictly declines in s², and can be negative
-- statement:
--   Consider the §5 benchmark (no reporting, learning or monitoring) with a fixed target resource level $\bar k$. For parameters satisfying the standing assumptions and a variance parameter $s>0$ of the information gap, let $d=\xi_s d^b$ be the true environment, $\xi_s=\exp(sZ-s^2/2)$, $Z\sim N(0,1)$, and let
--   $$
--   \Delta(s)=\mathbb E\big[G^o(\bar k,w(d))-G(\bar k,d)\big]
--   $$
--   be the expected per-period value of product service outsourcing, where $w(d)$ is the benchmark payment ($c^S(\bar k,d^b)$ if $d\le d^b$, and $c^S(\bar k,d)$ otherwise), and let $\Delta_{\mathrm{full}}(s)$ be the same expectation with the full-observability payment $c^S(\bar k,d)$. Then:
--
--   1. **(a) Only upward drift matters.** For every $s>0$,
--   $$
--   \Delta(s)=\Delta_{\mathrm{full}}(s)-\mathbb E\Big[\mathbf 1\{d\le d^b\}\big(c^S(\bar k,d^b)-c^S(\bar k,d)\big)\Big],
--   $$
--   and the loss term $\mathbf 1\{d\le d^b\}\big(c^S(\bar k,d^b)-c^S(\bar k,d)\big)$ is nonnegative for every realisation. So partial observability affects the value only on the event that the belief lies above the actual environment.
--   2. **(b) Strict decline.** $s\mapsto\Delta(s)$ is strictly decreasing on $(0,\infty)$, i.e. $\Delta$ strictly declines in the variance $s^2$.
--   3. **(c) Possibly negative.** There are parameters satisfying the standing assumptions with a strictly more efficient provider, $\alpha<1$, and a strict product-value gain, $v<v^o$, and some $s>0$ with $\Delta(s)<0$.
--
--   Partial observability can thus negate the value of outsourcing even though the provider is more cost-efficient and the brand gains product value, with no switching cost involved.
--
--   **Formalization Note** The paper writes $\Delta_i=V^{TS}_i(d^b_i,s_i)-V^{DS}_i(d_i)$ but argues period by period; with $\bar k$ fixed no decision is left in a period, so $\Delta$ is formalized as the expected per-period value. Part (b) is stated in $s$ on $(0,\infty)$, equivalent to strict decrease in $s^2$. In part (c) the witness must have $\alpha<1$ and $v<v^o$, as the text after the proposition says; the switching cost $\tau$ is not part of $\Delta$. The standing assumptions include $\beta>0$ and $\bar k>0$ (the paper allows $\beta\ge0$).
-- source:
--   Wang, Li, Ma & Zhang, Product service outsourcing: impact of environment uncertainty and partial observability, accepted manuscript (MSOM 2024, doi:10.1287/msom.2022.0222), p. 20 (PDF 20), Proposition 4; proof pp. A-6–A-7 (PDF 38–39)

import Mathlib
import Definitions.Def_PSOutsourcing_PartialObs_Model

open MeasureTheory ProbabilityTheory

namespace PSOutsourcing.PartialObs

theorem proposition_4 :
    (∀ P : Params, P.Standing →
      (∀ s : ℝ, 0 < s →
        delta P s = deltaFull P s
          - ∫ z, (if xi s z * P.db ≤ P.db
                  then costS P P.kbar P.db - costS P P.kbar (xi s z * P.db) else 0)
              ∂(gaussianReal 0 1)
        ∧ ∀ z : ℝ, 0 ≤ (if xi s z * P.db ≤ P.db
                  then costS P P.kbar P.db - costS P P.kbar (xi s z * P.db) else 0)) ∧
      StrictAntiOn (delta P) (Set.Ioi 0)) ∧
    (∃ P : Params, P.Standing ∧ P.α < 1 ∧ P.v < P.vo ∧ ∃ s : ℝ, 0 < s ∧ delta P s < 0) := by sorry

end PSOutsourcing.PartialObs
