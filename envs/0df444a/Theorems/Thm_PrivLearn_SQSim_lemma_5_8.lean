-- Prove2me | Theorems.Thm_PrivLearn_SQSim_lemma_5_8
-- name    : PrivLearn.SQSim.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:48:18.175619+00:00
-- url     : https://prove2.me/theorems/cda97acc-e126-446a-b85a-7c2f0965e196
-- title:
--   Lemma 5.8 — every ε-local algorithm making t queries is simulated by an SQ algorithm with O(t·e^ε) expected queries of tolerance β/(3e^{2ε}t) up to statistical difference β
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $D$ be a measurable space with a point $u_0$, let $\varepsilon>0$, $0<\beta\le1$, and let $n$ and $t\ge1$ be integers. For every (possibly interactive) $\varepsilon$-local algorithm $A$ on databases in $D^n$ making $t$ queries to its LR oracle, there exists an SQ algorithm $B$, depending only on $A$ and the parameters, such that:
--
--   1. every query of $B$ has a measurable $[-1,1]$-valued query function and tolerance
--
--   $$\tau=\frac{\beta}{3e^{2\varepsilon}t};$$
--
--   2. for every probability distribution $P$ on $D$ and every valid SQ oracle for $P$, $B$ makes in expectation at most $C\,t\,e^{\varepsilon}$ queries, and the statistical difference between the output distribution of $B$ and the output distribution of $A$ on a database $z\sim P^n$ of i.i.d. entries is at most $\beta$.
--
--   This is one direction of the equivalence between local algorithms and statistical query algorithms (§5.1): together with the simulation of SQ algorithms by local algorithms (Theorem 5.7) it shows that learnability in the local model coincides with SQ learnability, which is how the paper transfers SQ lower bounds to locally private learning.
--
--   **Formalization Note.** "$O(t\cdot e^{\varepsilon})$ queries" is the constant $C$, quantified before every other object. "$\tau=\Theta(\beta/(e^{2\varepsilon}t))$" is witnessed by the proof's exact choice $\beta/(3e^{2\varepsilon}t)$. The statement is the adaptive version, for all local algorithms; it contains the noninteractive case. The paper's parenthetical refinement "noninteractive $A$ yields nonadaptive $B$" is not formalized (see Claim 5.9). $B$ is chosen before $P$ and sees $P$ only through the answers of an adversarial, history-dependent oracle; its queries are $[-1,1]$-valued, which is what gives the tolerance its meaning. The hypotheses $\varepsilon>0$, $\beta\le1$ and $t\ge1$ are implicit in the paper. Randomizers have discrete output.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 21, Lemma 5.8 (proof via Claims 5.9 and 5.10, pp. 22–24)

import Mathlib
import Definitions.Def_PrivLearn_SQSim_Privacy
import Definitions.Def_PrivLearn_SQSim_LocalAlg
import Definitions.Def_PrivLearn_SQSim_SQAlg
import Definitions.Def_PrivLearn_SQSim_Estimate

open MeasureTheory

namespace PrivLearn.SQSim

/-- Lemma 5.8 (p. 21), adaptive form: there is an absolute constant `C > 0` such that for every
(interactive) ε-local algorithm `A` making `t` queries to `LR_z` there is an SQ algorithm `B`,
built from `A` alone, whose queries are `[−1, 1]`-valued with tolerance `τ = β/(3e^{2ε}t)`, such
that for every distribution `P` and every valid SQ oracle for `P`, `B` makes at most `C t e^ε`
queries in expectation and the statistical difference between `B`'s output distribution and `A`'s
output distribution on a database of `n` i.i.d. draws from `P` is at most `β`. -/
theorem lemma_5_8 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Dom W Out : Type) [MeasurableSpace Dom] (n t : ℕ) (ε β : ℝ) (u₀ : Dom),
        0 < ε → 0 < β → β ≤ 1 → 1 ≤ t →
        ∀ A : LocalAlg Dom W Out n t ε,
          ∃ (σ : Type) (B : SQAlg Dom Out σ),
            B.AsksOnly (simTolerance ε β t) ∧
            ∀ (P : Measure Dom) [IsProbabilityMeasure P] (O : List σ → ℝ),
              B.IsValidOracle P O →
                B.expectedQueries O ≤ ENNReal.ofReal (C * t * Real.exp ε) ∧
                statDiff (B.outputLaw O) (A.iidOutputLaw P) ≤ ENNReal.ofReal β := by sorry

end PrivLearn.SQSim
