-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_Supplement_support_covering
-- name    : RandomCNFDeficiency.LowerBound.Supplement.support_covering
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:58:37.918425+00:00
-- url     : https://prove2.me/theorems/841f302a-89f1-404f-89ce-a4417a1a3981
-- title:
--   Lemma 4.2 — support covering gives PC degree at most $r+1$
-- statement:
--   Let $1\le r\le n$ be integers and let $F$ be an unsatisfiable CNF formula on $n$ variables whose clauses all have width at most $r$. Suppose $F$ covers the $r$-element variable sets: every $T\subseteq[n]$ with $|T|=r$ contains the variable set of some clause of $F$. Then, over every field $\mathbb F$, $F$ has a polynomial calculus refutation (with the explicit Boolean axioms $x_i^2-x_i$) of degree at most $r+1$:
--
--   $$\operatorname{Deg}_{\mathrm{PC},\mathbb F}(F)\le r+1.$$
--
--   This deterministic criterion turns a combinatorial covering property of clause supports into a degree upper bound valid over all fields simultaneously; Theorem 4.1 applies it to a random formula together with its one-step resolvents.
--
--   Differences from the source:
--   - encoding: variables x_1, …, x_n → Fin n with true representing 1; reason: the bijection i ↦ i+1 preserves every clause and assignment
--   - encoding: Deg_PC,𝔽(F) ≤ b over every field 𝔽 → for every field K in one universe there exists an ordinary PC refutation of F over K of degree at most b, compared in ℝ; reason: the minimum refutation degree is at most b iff such a refutation exists
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Lemma 4.2, printed p. 15, PDF p. 17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_PCDerivation
import Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_Covering
universe uCover
set_option autoImplicit false

namespace RandomCNFDeficiency.LowerBound.Supplement

open RandomCNFDeficiency.LowerBound

/-- Conneryd, STOC 2027 #332, Lemma 4.2 (support covering): for `1 ≤ r ≤ n`, an unsatisfiable
CNF whose clauses have width at most `r` and which covers the `r`-element variable sets has an
ordinary PC refutation of degree at most `r + 1` over every field. -/
theorem support_covering {n : ℕ} (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) (F : CNF n)
    (hunsat : ¬ Satisfiable F) (hwidth : ∀ C ∈ F, clauseWidth C ≤ r)
    (hcover : CoversSets (F : Set (Clause n)) r) :
    AllFieldsEasy.{uCover} F ((r : ℝ) + 1) := by sorry

end RandomCNFDeficiency.LowerBound.Supplement
