-- Prove2me | Theorems.Thm_WatsonPseudodeterminism_MASeparation_nbpp_amplification
-- name    : WatsonPseudodeterminism.MASeparation.nbpp_amplification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:31:58.724226+00:00
-- url     : https://prove2.me/theorems/dcc8b94e-6037-4ed2-b15b-bf5e1cd87719
-- title:
--   §1.1 — Constant-error amplification for N·BPP
-- statement:
--   For every real target error $\varepsilon>0$ there is a natural number $C$, depending only on $\varepsilon$, such that for every two-party partial function $F$ and every natural cost $d$,
--
--   $$F\text{ has a }1/3\text{-error N·BPP protocol of cost }d\ \Longrightarrow\ F\text{ has an }\varepsilon\text{-error N·BPP protocol of cost }Cd.$$
--
--   The conclusion retains the bound of $2^{Cd}$ witnesses and depth $Cd$, and every witness has acceptance in $[0,\varepsilon]\cup[1-\varepsilon,1]$ on every valid input. This item states the N·BPP clause of the source's sentence, the clause used in §4; other models' amplification clauses are outside this mission's scope. It allows every positive target error, including the trivial regime $\varepsilon\ge1/3$.
--
--   Differences from the source:
--   - encoding: a set of at most 2^d distributions over depth-d protocols → an indexed family of k PMFs with k ≤ 2^d and support depth at most d; reason: duplicate indices do not change the represented set; every source distribution is represented and zero-mass trees do not affect the law
--   - generalization: equal-length finite bit-string input spaces → arbitrary types X and Y; reason: finite bit-string spaces are particular types; independent repetition uses no finiteness assumption
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §1.1, amplification sentence, p. 4 (N·BPP clause; used in §4, p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_Models

namespace WatsonPseudodeterminism.MASeparation

/-- §1.1, p. 4, N·BPP clause: every positive target error has a uniform cost factor. -/
theorem nbpp_amplification (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℕ, ∀ (X Y : Type) (F : PartialFn X Y) (d : ℕ),
      NBPPProtocol F d → NBPPProtocolErr ε F (C * d) := by sorry

end WatsonPseudodeterminism.MASeparation
