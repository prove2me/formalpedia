-- Prove2me | Theorems.Thm_ShuffleDecoys_Hierarchy_lemma_3_1
-- name    : ShuffleDecoys.Hierarchy.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:23:20.946214+00:00
-- url     : https://prove2.me/theorems/f8a8a137-9665-48be-8482-40999faa4baa
-- title:
--   Lemma 3.1 — an integer-valued variable with variance σ² is at total variation ≥ 3/(16(σ + 1)) from its unit shift
-- statement:
--   Let $S$ be an integer-valued random variable with finite variance $\operatorname{Var}(S)=\sigma^2$. Then
--   $$D_{\mathrm{TV}}\big(\mathrm{Law}(S),\mathrm{Law}(S+1)\big)\ \ge\ \frac{3}{16(\sigma+1)}.$$
--   A unit shift cannot be hidden by integer noise of small spread: this is the probabilistic ingredient of every leakage lower bound for independent decoys.
--
--   Differences from the source:
--   - encoding: the random variable $S$ → its law, a `PMF ℤ`, with $\mathrm{Law}(S+1)$ its image under $k\mapsto k+1$; reason: the statement depends only on the law.
--   - encoding: "finite variance" → $\sum_kS(k)k^2<\infty$ (`HasFiniteVar`), $\sigma=\sqrt{\texttt{pmfVar}\,S}$; reason: the same condition and the same $\sigma$.
-- source:
--   Su, Cheng, Wang, The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model, STOC 2027 submission (manuscript sha256 445baceb…), p. 16, Lemma 3.1

import Mathlib
import Definitions.Def_ShuffleDecoys_Hierarchy_Info
import Definitions.Def_ShuffleDecoys_Hierarchy_Model

open scoped ENNReal

namespace ShuffleDecoys.Hierarchy

/-- Lemma 3.1: an integer-valued random variable with law `S` and finite variance `σ²` satisfies
`D_TV(Law(S), Law(S + 1)) ≥ 3/(16(σ + 1))`. -/
theorem lemma_3_1 (S : PMF ℤ) (hS : HasFiniteVar S) :
    3 / (16 * (Real.sqrt (pmfVar S) + 1)) ≤ tvDist S (S.map fun k => k + 1) := by sorry

end ShuffleDecoys.Hierarchy
