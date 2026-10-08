-- Prove2me | Theorems.Thm_PrivLearn_SQSim_claim_5_9
-- name    : PrivLearn.SQSim.claim_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:48:08.683756+00:00
-- url     : https://prove2.me/theorems/cca42a97-a0d3-4e5a-8a55-85da64fdf606
-- title:
--   Claim 5.9 — an SQ algorithm with ≤ 2t·e^ε expected queries of tolerance β/(3e^{2ε}t) simulates any noninteractive ε-local algorithm up to statistical difference β
-- statement:
--   Let $D$ be a measurable space with a point $u_0$, let $\varepsilon>0$, $0<\beta\le1$, and let $n$ and $t\ge1$ be integers. For every **noninteractive** $\varepsilon$-local algorithm $A$ on databases in $D^n$ making $t$ queries to its LR oracle, there exists an SQ algorithm $B$, depending only on $A$ and the parameters, such that:
--
--   1. every query of $B$ has a measurable $[-1,1]$-valued query function and tolerance $\tau=\beta/(3e^{2\varepsilon}t)$;
--   2. for every probability distribution $P$ on $D$ and every valid SQ oracle for $P$ (answers within $\tau$ of the true expectation, chosen adversarially and adaptively), $B$ makes in expectation at most $2t\,e^{\varepsilon}$ queries, and
--
--   $$\mathrm{SD}\bigl(\text{output law of }B,\ \text{output law of }A\text{ on }z\sim P^n\bigr)\le\beta .$$
--
--   This is the noninteractive half of Lemma 5.8: local randomizers applied to i.i.d. data can be replaced by statistical queries, with a constant-factor overhead $e^{\varepsilon}$ in the number of queries.
--
--   **Formalization Note.** The paper states "in expectation makes $t\cdot e^{\varepsilon}$ queries"; its proof gives at most $\frac{1+\varphi}{1-\varphi}e^{\varepsilon}\le2e^{\varepsilon}$ iterations, one query each, per simulated randomizer, so the statement uses the bound $2t\,e^{\varepsilon}$. The paper's $\tau=\Theta(\beta/(e^{2\varepsilon}t))$ is witnessed by the proof's exact choice $\beta/(3e^{2\varepsilon}t)$. The paper calls $B$ **nonadaptive**; that qualifier is not formalized (the simulation decides from each answer whether to stop and so which randomizer the next query belongs to, so it does not prepare its queries before receiving answers in the sense of Definition 5.5). The hypotheses $\beta\le1$, $t\ge1$ (so that $\varphi\le1/3$ and $\tau$ is defined) and $\varepsilon>0$ (the query divides by $e^{\varepsilon}-e^{-\varepsilon}$) are implicit in the paper. $B$ is chosen before $P$, so it cannot depend on the distribution, and the bounds hold for every valid oracle.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 22, Claim 5.9 (proof pp. 22–23)

import Mathlib
import Definitions.Def_PrivLearn_SQSim_Privacy
import Definitions.Def_PrivLearn_SQSim_LocalAlg
import Definitions.Def_PrivLearn_SQSim_SQAlg
import Definitions.Def_PrivLearn_SQSim_Estimate

open MeasureTheory

namespace PrivLearn.SQSim

/-- Claim 5.9 (p. 22), with the expected query count the proof gives (`≤ 2 t e^ε`, p. 23) and
without the "nonadaptive" qualifier on `B`: for every noninteractive ε-local algorithm `A` making
`t` queries to `LR_z` there is an SQ algorithm `B`, built from `A` alone, whose queries are
`[−1, 1]`-valued with tolerance `τ = β/(3e^{2ε}t)`, such that for every distribution `P` and every
valid SQ oracle for `P`, `B` makes at most `2 t e^ε` queries in expectation and the statistical
difference between `B`'s output distribution and `A`'s output distribution on a database of `n`
i.i.d. draws from `P` is at most `β`. -/
theorem claim_5_9 :
    ∀ (Dom W Out : Type) [MeasurableSpace Dom] (n t : ℕ) (ε β : ℝ) (u₀ : Dom),
      0 < ε → 0 < β → β ≤ 1 → 1 ≤ t →
      ∀ A : LocalAlg Dom W Out n t ε, A.IsNoninteractive →
        ∃ (σ : Type) (B : SQAlg Dom Out σ),
          B.AsksOnly (simTolerance ε β t) ∧
          ∀ (P : Measure Dom) [IsProbabilityMeasure P] (O : List σ → ℝ),
            B.IsValidOracle P O →
              B.expectedQueries O ≤ ENNReal.ofReal (2 * t * Real.exp ε) ∧
              statDiff (B.outputLaw O) (A.iidOutputLaw P) ≤ ENNReal.ofReal β := by sorry

end PrivLearn.SQSim
