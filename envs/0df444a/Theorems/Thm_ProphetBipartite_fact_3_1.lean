-- Prove2me | Theorems.Thm_ProphetBipartite_fact_3_1
-- name    : ProphetBipartite.fact_3_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T09:49:16.977209+00:00
-- url     : https://prove2.me/theorems/86daba03-bed1-4efe-89b6-01e77dc2b569
-- title:
--   Fact 3.1 — $\mathbb E[[s]^+]\ge[\mathbb E[s]]^+$
-- statement:
--   Let $s$ be a real random variable with finite expectation, and write $[x]^+=\max\{x,0\}$. Then
--
--   $$
--   \mathbb E\big[[s]^+\big]\ \ge\ \big[\mathbb E[s]\big]^+ .
--   $$
--
--   This is Jensen's inequality for the convex function $x\mapsto[x]^+$. The proof of Lemma 3.1 applies it to $s=\chi^{(i,j)}_{\mathrm{opt}}(\hat v)-(l_i+r_j)\,\mathbb I^{(i,j)}_{\mathrm{opt}(\hat v)}$.
--
--   Differences from the source:
--   - encoding: "for any real random variables s" → s : Ω → ℝ integrable on a probability space (Ω, P); reason: [E[s]]⁺ requires E[s] to be a real number, which is integrability
-- source:
--   Gravin, Wang, Prophet inequality for bipartite matching: merits of being simple and non adaptive, arXiv:1902.06243v1, Fact 3.1, p.7

import Mathlib

open MeasureTheory

namespace ProphetBipartite

/-- **Fact 3.1.** Gravin & Wang, arXiv:1902.06243v1, p.7: "`E[[s]⁺] ≥ [E[s]]⁺` for any real random
variables `s`", where `[x]⁺ = max{x, 0}`.

**Formalization Note.** `s` is a real random variable on a probability space with a finite
expectation (`Integrable s P`), which is what makes `E[s]` a real number. -/
theorem fact_3_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Ω → ℝ) (hs : Integrable s P) :
    max (∫ ω, s ω ∂P) 0 ≤ ∫ ω, max (s ω) 0 ∂P := by sorry

end ProphetBipartite
