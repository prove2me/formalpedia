-- Prove2me | Theorems.Thm_PrivateRelease_Continuous_corollary_5_2
-- name    : PrivateRelease.Continuous.corollary_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:08:19.438335+00:00
-- url     : https://prove2.me/theorems/ec2b861f-1b3e-4270-a9ae-dfdf7579e400
-- title:
--   Corollary 5.2 — no ε-DP mechanism is (α, δ)-useful for interval queries on real-valued databases when α, δ < 1/2
-- statement:
--   Let $n \ge 1$, $\varepsilon \ge 0$, and $\alpha, \delta < 1/2$. Let $A$ be a randomized mechanism mapping each real-valued database $z \in \mathbb R^n$ to a probability distribution $A(z)$ on a measurable space $O$ of outputs, and let $\mathrm{ans}(o, a, b) \in \mathbb R$ be the answer that output $o$ gives to the interval query $Q_{[a,b]}$, where
--   $$
--   Q_{[a,b]}(z) = \frac{\#\{\, i : a \le z_i \le b \,\}}{n} \qquad (a \le b).
--   $$
--   Assume that for each fixed $a, b$ the map $o \mapsto \mathrm{ans}(o,a,b)$ is measurable, and that $A$ is $\varepsilon$-differentially private (for databases differing in one entry and every measurable set $S$ of outputs, $\Pr[A(z)\in S] \le e^{\varepsilon}\Pr[A(z')\in S]$). Then $A$ is **not** $(\alpha,\delta)$-useful for interval queries: there is a database $z \in \mathbb R^n$ with
--   $$
--   \Pr_{o \sim A(z)}\Big[\ \forall\, a \le b:\ \big|\mathrm{ans}(o,a,b) - Q_{[a,b]}(z)\big| \le \alpha\ \Big] \ <\ 1 - \delta .
--   $$
--
--   The result shows that the paper's positive results, which release synthetic data accurate for all queries of a class, cannot extend to a continuous data universe even for the simplest class with infinitely many queries. It is the reason the paper discretizes the domain (§§3–4) or relaxes usefulness (§6).
--
--   **Formalization Note.** The paper states the result for mechanisms that output synthetic data; here the output is any measurable space with a measurable readout, which includes synthetic data (a finite real database $\hat D$ with $\mathrm{ans}(\hat D,a,b) = Q_{[a,b]}(\hat D)$) and gives a stronger negative result. The measurability of the readout cannot be dropped: with a non-measurable readout, disjoint usefulness events of different databases could each have outer measure one. The usefulness event is an uncountable intersection; its probability is the outer measure. The clause "nor for any class $C$ that generalizes interval queries to higher dimensions" is not formalized, because "generalizes" is not defined in the paper. Neighbours replace one entry; $n \ge 1$ is assumed (at $n = 0$ Lean's $0/0 = 0$ makes every query trivially answerable). The paper's hypothesis $\delta < 1/2$ is kept as printed.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 15, Corollary 5.2 (interval-query clause)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivateRelease_Continuous_Queries

open MeasureTheory PrivLearn.Generic

namespace PrivateRelease.Continuous

theorem corollary_5_2 (n : ℕ) (O : Type) [MeasurableSpace O] (A : (Fin n → ℝ) → Measure O)
    (ans : O → ℝ → ℝ → ℝ) (ε α δ : ℝ)
    (hn : 1 ≤ n) (hε : 0 ≤ ε) (hα : α < 1 / 2) (hδ : δ < 1 / 2)
    (hA : ∀ z, IsProbabilityMeasure (A z)) (hans : ∀ a b : ℝ, Measurable fun o => ans o a b)
    (hdp : IsDP A ε) :
    ¬ UsefulIntervals A ans α δ := by sorry

end PrivateRelease.Continuous
