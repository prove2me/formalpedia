-- Prove2me | Theorems.Thm_UniqueOptScores_Supplement_theorem_1_1
-- name    : UniqueOptScores.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:55:44.237674+00:00
-- url     : https://prove2.me/theorems/b096d232-10e3-4176-8e9b-7cdd037bd7a9
-- title:
--   Theorem 1.1 — $\mathrm{UO_P}\subseteq\mathrm{DP}$ implies $\mathrm{coNP}\subseteq\mathrm{NP}/\mathrm{poly}$ and $\mathrm{PH}=\mathrm S_2^{\mathrm{NP}}$
-- statement:
--   This is the paper's ordinary-world (unrelativized) separation of unique optimality from exact-one acceptance.
--
--   Let $\mathrm{UO_P}$ be the class of languages decided by unique optimality with polynomially bounded scores, $\mathrm{DP}=\{L_1\cap L_2: L_1\in\mathrm{NP},\,L_2\in\mathrm{coNP}\}$, $\mathrm{US}$ the class of exact-one acceptance, $\mathrm{PH}=\bigcup_{k\ge0}\Sigma^{\mathrm P}_k$ the polynomial hierarchy, $\mathrm S_2^{\mathrm{NP}}$ symmetric alternation with a $\mathrm P^{\mathrm{NP}}$ predicate, $\mathrm{NP}/\mathrm{poly}$ NP with polynomial-length advice, and $\mathrm{UOCLIQUE}$ the unique maximum clique problem. Then:
--
--   1. If $\mathrm{UO_P}\subseteq\mathrm{DP}$, then
--   $$\mathrm{coNP}\subseteq\mathrm{NP}/\mathrm{poly}\qquad\text{and}\qquad \mathrm{PH}=\mathrm S_2^{\mathrm{NP}} .$$
--   2. Consequently, if $\mathrm{PH}\ne\mathrm S_2^{\mathrm{NP}}$, then
--   $$\mathrm{UO_P}\not\subseteq\mathrm{DP},\qquad \mathrm{US}\subsetneq\mathrm{UO_P},\qquad \mathrm{UOCLIQUE}\notin\mathrm{DP}.$$
--
--   Under the noncollapse assumption, optimality adds power to exact-one acceptance, and the $\mathrm{DP}$ upper bound for $\mathrm{US}$ does not extend to $\mathrm{UO_P}$.
--
--   **Formalization Note** All classes are unrelativized: the base mission's relativized classes at the empty oracle. Both sentences are stated in full, including the strict inclusion $\mathrm{US}\subsetneq\mathrm{UO_P}$; no result cited in the proof is assumed.
--
--   Differences from the source:
--   - encoding: UOCLIQUE on graphs, encoding unspecified → words of length n² read as symmetric zero-diagonal adjacency matrices; other words are not in UOCLIQUE; reason: the page fixes no encoding; any polynomial-time equivalent encoding with polynomial-time decidable validity gives the same statement
--   - encoding: P^NP: polynomial-time machine with an oracle for a fixed NP-complete language → clocked machine with oracle some B ∈ NP ∅; reason: same class: an NP-complete language is in NP, and a query to any B ∈ NP is one query to an NP-complete language after a reduction
--   - encoding: polynomially bounded quantifier blocks (Σ_k, S₂^NP) over {0,1}^{p(|x|)}; R a Boolean predicate in P^NP → blocks of exact length p(|x|), concatenated into one string; R as the P^NP language of triples pair x (pair y z) on which R = 1; reason: padding equivalence and the standard identification of a Boolean predicate with its 1-set; same classes
--   - encoding: unrelativized NP, coNP, DP, US, UO_P → the base mission classes at the empty oracle (NP ∅, coNP ∅, DP ∅, US ∅, UOP ∅), verifier form, clocks valid for every oracle; reason: p.15 omits oracle superscripts in the unrelativized setting; the base classes are the paper's definitions
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Theorem 1.1 (restated), p.19 (PDF p.20); also Theorem 1.1, p.3 (PDF p.4); definitions §3.2, p.14 (PDF p.15) and §1.1, p.1 (PDF p.2)

import Mathlib
import Definitions.Def_UniqueOptScores_NP
import Definitions.Def_UniqueOptScores_coNP
import Definitions.Def_UniqueOptScores_DP
import Definitions.Def_UniqueOptScores_US
import Definitions.Def_UniqueOptScores_UOP
import Definitions.Def_UniqueOptScores_Supplement_PH
import Definitions.Def_UniqueOptScores_Supplement_S2NP
import Definitions.Def_UniqueOptScores_Supplement_NPpoly
import Definitions.Def_UniqueOptScores_Supplement_UOCLIQUE

namespace UniqueOptScores

namespace Supplement

/-- **Theorem 1.1 (restated): UO_P ⊆ DP collapses PH to S^NP_2.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Theorem 1.1 (restated), p.19 (PDF p.20); also Theorem 1.1, p.3 (PDF p.4): "If UOP ⊆ DP, then
coNP ⊆ NP/poly and PH = S^NP_2. Therefore, if PH ≠ S^NP_2, then UOP ⊄ DP, US ⊊ UOP,
UOCLIQUE ∉ DP."

**Formalization Note.** Unrelativized setting (p.15: "We omit oracle superscripts in the
unrelativized setting"): UO_P, DP, US, NP and coNP are the base mission's classes at the empty
oracle, `UOP ∅`, `DP ∅`, `US ∅`, `NP ∅`, `coNP ∅`. `PH`, `S2NP`, `NPpoly` and `UOCLIQUE` are this
supplement's definitions (p.14 and p.1). `US ∅ ⊂ UOP ∅` is strict inclusion. Both sentences of the
theorem are stated; no cited result of the proof is assumed. -/
theorem theorem_1_1 :
    (UOP ∅ ⊆ DP ∅ → coNP ∅ ⊆ NPpoly ∧ PH = S2NP) ∧
      (PH ≠ S2NP → ¬ (UOP ∅ ⊆ DP ∅) ∧ US ∅ ⊂ UOP ∅ ∧ UOCLIQUE ∉ DP ∅) := by sorry

end Supplement

end UniqueOptScores
