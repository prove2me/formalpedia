-- Prove2me | Theorems.Thm_SecondBestBT_Supplement_theorem_6_2
-- name    : SecondBestBT.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:40:57.206938+00:00
-- url     : https://prove2.me/theorems/d6f9aa41-f87d-4ae2-8a4d-b13aedb6b9bf
-- title:
--   Theorem 6.2 — the ratio $1/2$ is tight
-- statement:
--   No mechanism that is BIC, interim IR and ex-ante WBB can guarantee a worst-case efficiency ratio exceeding $1/2$: for every $\varepsilon>0$ there exist independent priors $F_S,F_B$ on $[0,1]$ with finite, positive first-best gains from trade such that
--   $$
--   \mathrm{SB}_{F_S,F_B}\ <\ \Big(\frac12+\varepsilon\Big)\,\mathrm{FB}_{F_S,F_B}.
--   $$
--   The inequality holds both for the second-best benchmark over mechanisms whose BIC and interim-IR constraints hold at every type in $[0,1]$ and for the benchmark over types in $[0,\infty)$, the class of the main theorem; the priors are in particular priors on $[0,\infty)$.
--
--   Here $\mathrm{FB}_{F_S,F_B}=\mathbb E[(b-s)^+]$ and $\mathrm{SB}_{F_S,F_B}$ is the supremum of the gains from trade over all well-defined BIC, interim-IR, ex-ante weakly budget-balanced mechanisms (signed transfers allowed). Together with Theorem 5.14 this shows that $1/2$ is the exact worst-case efficiency ratio of the second-best mechanism.
--
--   Differences from the source:
--   - reading: "No mechanism that is BIC, interim IR, and ex-ante WBB can guarantee a worst-case efficiency ratio exceeding 1/2" → for every $\varepsilon>0$ there are priors with $0<\mathrm{FB}<\infty$ and $\mathrm{SB}<(1/2+\varepsilon)\mathrm{FB}$; reason: the form stated by the proof (p.60: "for every ϵ > 0 there exists a prior pair such that SB/FB < 1/2 + ϵ") and by Theorem 1.1 (p.1)
--   - generalization: witness priors in the class of the main theorem (priors on $[0,\infty)$, benchmark over types in $[0,\infty)$) → witness priors on $[0,1]$, and the bound for both type sets $[0,1]$ and $[0,\infty)$; reason: priors on $[0,1]$ are priors on $[0,\infty)$ and the $[0,\infty)$ conjunct is the source's claim; the $[0,1]$ conjunct adds the Section 6 setting, whose benchmark has fewer constraints and is at least as large
--   - encoding: "finite positive first-best GFT" → integrability of $(b-s)^+$ under the product measure and $0<\mathrm{FB}$; reason: FB is the integral of a nonnegative function, so finiteness is its integrability, as in the published goal
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Theorem 6.2, p.27; proof of Theorem 6.2, p.60; Theorem 1.1, p.1

import Mathlib
import Definitions.Def_SecondBestBT_IsPriorOn
import Definitions.Def_SecondBestBT_secondBest
import Definitions.Def_SecondBestBT_firstBest

open MeasureTheory

namespace SecondBestBT.Supplement

/-- **Theorem 6.2** (tightness of `1/2`; Liu–Qin–Ren–Wang, *Second-Best Bilateral Trade is 1/2
Efficient*, arXiv:2606.03849, held version sha256 17184930…, Theorem 6.2, p.27; its proof,
p.60: "for every ε > 0 there exists a prior pair such that SB/FB < 1/2 + ε"; Theorem 1.1, p.1).
No mechanism that is BIC, interim IR and ex-ante WBB can guarantee a worst-case efficiency ratio
exceeding `1/2`: for every `ε > 0` there are priors `F_S, F_B` with finite positive first-best GFT
and `SB_{F_S,F_B} < (1/2 + ε) FB_{F_S,F_B}`.

**Formalization Note** `SB` is the published `secondBest` (supremum of GFT over well-defined,
BIC, interim-IR, ex-ante WBB mechanisms whose constraints hold at every type of `T`), `FB` the
published `firstBest`. The witnesses are priors on `[0, 1]` (the family of Section 6), which are
in particular priors on `[0, ∞)`. The bound is stated both for the type set `[0, 1]` of
Section 6 and for the type set `[0, ∞)` of the main theorem (Theorem 5.14, Theorem 1.1). -/
theorem theorem_6_2 (ε : ℝ) (hε : 0 < ε) :
    ∃ μS μB : Measure ℝ, IsPriorOn (Set.Icc 0 1) μS ∧ IsPriorOn (Set.Icc 0 1) μB ∧
      Integrable (fun p : ℝ × ℝ => max (p.2 - p.1) 0) (μS.prod μB) ∧
      0 < firstBest μS μB ∧
      secondBest (Set.Icc 0 1) μS μB < (1 / 2 + ε) * firstBest μS μB ∧
      secondBest (Set.Ici 0) μS μB < (1 / 2 + ε) * firstBest μS μB := by sorry

end SecondBestBT.Supplement
