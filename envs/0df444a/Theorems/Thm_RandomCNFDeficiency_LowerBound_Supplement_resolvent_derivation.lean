-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_Supplement_resolvent_derivation
-- name    : RandomCNFDeficiency.LowerBound.Supplement.resolvent_derivation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:59:11.880611+00:00
-- url     : https://prove2.me/theorems/fc403b4c-805a-42d6-81cb-b92262d46d85
-- title:
--   Fact 4.5 — one-step resolvents are derivable in degree $2k-1$
-- statement:
--   Let $k\ge2$ and let $F$ be a CNF. Let $R=A\vee B$ be a clause of $\mathrm{Resol}(F)$, i.e. the resolvent of two width-$k$ clauses $z\vee A$ and $\neg z\vee B$ of $F$ whose variable sets meet exactly in $z$. Then over every field $\mathbb F$ the clause polynomial $p_R$ has a polynomial calculus derivation from $F$ (with the Boolean axioms) of degree at most
--
--   $$2k-1.$$
--
--   Adding these resolvents to $F$ therefore costs no more than degree $2k-1$, which is below the target degree $r+1$ of Theorem 4.1.
--
--   Differences from the source:
--   - encoding: variables x_1, …, x_n → Fin n with true representing 1; reason: the bijection i ↦ i+1 preserves every clause and assignment
--   - generalization: F a k-CNF (the random formula of Theorem 4.1) → an arbitrary CNF F, with Resol(F) formed from pairs of width-k clauses of F; reason: the derivation uses only the two width-k parents; for a k-CNF this Resol(F) is exactly the source's set
--   - encoding: derivable from F in degree at most 2k − 1 over every field → for every field K (in one universe) a PC derivation list from F ending in p_R with maximal total degree ≤ 2k − 1; reason: same notion of derivation
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Fact 4.5, printed p. 17, PDF p. 19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_PCDerivation
import Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_Covering
universe uRes
set_option autoImplicit false

namespace RandomCNFDeficiency.LowerBound.Supplement

open RandomCNFDeficiency.LowerBound

/-- Conneryd, STOC 2027 #332, Fact 4.5: for `k ≥ 2`, the clause polynomial of every clause of
`Resol(F)` has an ordinary PC derivation from `F` of degree at most `2k - 1`, over every field. -/
theorem resolvent_derivation {n : ℕ} (k : ℕ) (hk : 2 ≤ k) (F : CNF n) (R : Clause n)
    (hR : R ∈ Resol F k) (K : Type uRes) [Field K] :
    ∃ π : List (MvPolynomial (Fin n) K),
      IsPCDerivation F π (clausePolynomial R) ∧ pcDegree π ≤ 2 * k - 1 := by sorry

end RandomCNFDeficiency.LowerBound.Supplement
