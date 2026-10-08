-- Prove2me | Theorems.Thm_PrivLearn_LocalSim_theorem_5_7
-- name    : PrivLearn.LocalSim.theorem_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:23.692124+00:00
-- url     : https://prove2.me/theorems/2eb76f42-b74c-4755-8cdb-bb3d54d9703a
-- title:
--   Theorem 5.7 — an ε-local algorithm simulates any t-query SQ algorithm
-- statement:
--   There is an absolute constant $c>0$ with the following property. Let $\mathcal A_{SQ}$ be an SQ algorithm on a domain $D$ that makes $t$ queries $g_k:D\to[-b,b]$, with $|g_k|\le b$, and let $b,\varepsilon>0$. Consider the simulation of $\mathcal A_{SQ}$ that answers the $k$-th query by running $\mathcal A_{g_k}(m,\varepsilon,LR_z)$ on the $k$-th block of $m$ previously unused entries of the database $z$, and outputs what $\mathcal A_{SQ}$ outputs on the simulated answers.
--
--   1. **Privacy.** For every block size $m$ and every database size $n\ge tm$, the simulation is $\varepsilon$-differentially private.
--   2. **Accuracy.** Let every query have tolerance at least $\tau$, where $\tau>0$, $0<\beta<1$, $\varepsilon\le1$ and $\varepsilon\tau\le4b$. If the block size satisfies
--   $$m\ \ge\ c\cdot\frac{\ln(t/\beta)\,b^2}{\varepsilon^2\tau^2}$$
--   (so the simulation uses $tm\ \ge\ c\,t\ln(t/\beta)b^2/(\varepsilon^2\tau^2)$ entries, and the database has $n\ge tm$ entries) and the entries of $z$ are i.i.d. from $P$, then with probability at least $1-\beta$ over the database and the noise, every simulated answer $a_k$ is within the tolerance $\tau_k$ of $\mathbb E_{u\sim P}[g_k(u)]$ for the query $g_k$ actually asked. The simulated answers are then the answers of a valid SQ oracle $SQ_P$, so the simulation gives the same output as $\mathcal A_{SQ}$ run against that oracle.
--
--   This is the direction "SQ ⊆ local" of the equivalence between private learning in the local model and SQ learning.
--
--   **Formalization Note.** "For sufficiently large constant $c$" is $\exists c>0$ before every other quantifier; the block size is $n'=c\log(1/\beta')b^2/(\varepsilon^2\tau^2)$ with $\beta'=\beta/t$, so $\log(1/\beta')=\log(t/\beta)$; we use the natural logarithm (the paper's base 2 only changes $c$) and allow any block size above the threshold. The SQ algorithm is a deterministic adaptive strategy (a randomized one is a mixture over its coins), with exactly $t$ queries. "Gives the same output as $\mathcal A_{SQ}$" is formalized as: the simulated transcript is a valid transcript of $\mathcal A_{SQ}$ against $SQ_P$; the accuracy claim bounds the measure of the failure event by $\beta$. Privacy is stated for the output law of the simulation and assumes the output map is measurable (otherwise the push-forward is the zero measure). Added hypotheses: each query is jointly measurable in (earlier answers, input), which the paper does not discuss and which makes the simulated answers measurable functions of the noise and the data; $\varepsilon\le1$ and $\varepsilon\tau\le4b$ in the accuracy claim only, without which it is false already for $t=1$ (see Lemma 5.6); the privacy claim holds for every $\varepsilon>0$. "Noninteractive if $\mathcal A_{SQ}$ is nonadaptive" and "efficient if $\mathcal A_{SQ}$ is efficient" are not formalized.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 21, Theorem 5.7 (with the Simulation paragraph above it)

import Mathlib
import Definitions.Def_PrivLearn_LocalSim_Privacy
import Definitions.Def_PrivLearn_LocalSim_Simulation

namespace PrivLearn.LocalSim

open MeasureTheory

/-- Theorem 5.7 (Local simulation of SQ, p. 21). There is an absolute constant `c > 0` such that
for every SQ algorithm `A` making `t` queries `g_k : Dom → [−b, b]`, each with tolerance at least
`τ`:

1. (privacy) for every block size `m` and every database size `n ≥ t m`, the simulation, which
   answers the `k`-th query by running `A_{g_k}(m, ε, LR_z)` on the `k`-th block of `m` entries of
   `z`, and outputs `A`'s output on the simulated answers, is ε-differentially private;
2. (accuracy) if the block size is `m ≥ c · ln(t/β) b² / (ε² τ²)` (so `n ≥ t m` entries are used)
   and the entries of `z` are i.i.d. from `P`, then with probability at least `1 − β` the
   simulated answers form a transcript of `A` against a valid SQ oracle `SQ_P`, so the simulation
   gives the same output as `A` run against that oracle: the failure event has measure `≤ β`.

The accuracy claim is stated for `ε ≤ 1` and in the regime `ε τ ≤ 4 b`, without which it is false;
the privacy claim holds for every `ε > 0` and carries neither hypothesis. -/
theorem theorem_5_7 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Dom Out : Type) [MeasurableSpace Dom] [MeasurableSpace Out] (t : ℕ) (A : SQAlg Dom Out t)
        (b ε : ℝ),
        0 < b → 0 < ε →
        (∀ (k : Fin t) (a : Fin k → ℝ) (u : Dom), |A.query k a u| ≤ b) →
        (∀ k : Fin t, Measurable fun p : (Fin k → ℝ) × Dom => A.query k p.1 p.2) →
        -- privacy (for every ε > 0, every block size and every database)
        (Measurable A.output →
          ∀ (m n : ℕ) (h : t * m ≤ n),
            PrivLearn.Generic.IsDP (fun z : Fin n → Dom => simOutputLaw A b ε m h z) ε) ∧
        -- accuracy
        (∀ (τ β : ℝ), ε ≤ 1 → 0 < τ → ε * τ ≤ 4 * b → 0 < β → β < 1 →
          (∀ (k : Fin t) (a : Fin k → ℝ), τ ≤ A.tol k a) →
          ∀ (P : Measure Dom) [IsProbabilityMeasure P] (m n : ℕ) (h : t * m ≤ n),
            c * Real.log (t / β) * b ^ 2 / (ε ^ 2 * τ ^ 2) ≤ m →
            ((Measure.pi fun _ : Fin n => P).prod (noiseLaw t m b ε))
                {p | ¬ A.IsValidTranscript P (simTranscript A m h p.1 p.2)}
              ≤ ENNReal.ofReal β) := by sorry

end PrivLearn.LocalSim
