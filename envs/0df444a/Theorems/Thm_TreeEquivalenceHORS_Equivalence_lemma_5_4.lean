-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_4
-- name    : TreeEquivalenceHORS.Equivalence.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:23.641507+00:00
-- url     : https://prove2.me/theorems/9d189137-c142-4c4a-8d97-00b6852b707b
-- title:
--   Lemma 5.4 (Polynomial realization): $\mathrm{Pol}_0(\mathrm{Seed}_+,\mathrm{Seed}_-)$ and $\mathrm{Pol}_m(p,q)\Rightarrow\mathrm{Pol}_{m+1}(\mathrm{Next}_+pq,\mathrm{Next}_-pq)$
-- statement:
--   In every compiled scheme $G^\diamond_M$:
--   1. the seeds satisfy $\mathrm{Pol}_0(\mathrm{Seed}_+,\mathrm{Seed}_-)$;
--   2. for every $m$ and all closed $p,q:P$,
--   $$\mathrm{Pol}_m(p,q)\Longrightarrow\mathrm{Pol}_{m+1}(\mathrm{Next}_+\,p\,q,\ \mathrm{Next}_-\,p\,q).$$
--
--   Here $\mathrm{Pol}_m$ (Equation (19)) quantifies over all $u,v\in\mathbb N$, including $u<v$, and all numeral representations of them. The stored polynomial terms therefore track $C_m=(P^+_m,P^-_m)$, whose difference is $Z_m(u-v)$.
--
--   Differences from the source:
--   - encoding: Num(t, n) and Pol_m(p, q) are defined for closed terms t : N and p, q : P → `Num` and `Pol` include the conjuncts `typeOf [] t = some N` (resp. `P`); reason: the source defines the relations only on closed typed terms; the conjunct records that domain
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Lemma 5.4, printed p. 18 / PDF p. 20

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler

namespace TreeEquivalenceHORS.Equivalence

/-- **Lemma 5.4 (Polynomial realization)** (printed p. 18 / PDF p. 20), in every compiled scheme:
the seeds satisfy `Pol₀(Seed₊, Seed₋)`, and `Pol_m(p, q) ⟹ Pol_{m+1}(Next₊ p q, Next₋ p q)`. -/
theorem lemma_5_4 (side : Side) (M : Machine) :
    let G := compile side M
    Pol G 0 (.nt iSeedP) (.nt iSeedM) ∧
    ∀ (m : ℕ) (p q : Tm), Pol G m p q →
      Pol G (m + 1) (Tm.apps (.nt iNextP) [p, q]) (Tm.apps (.nt iNextM) [p, q]) := by sorry

end TreeEquivalenceHORS.Equivalence
