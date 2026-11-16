-- Prove2me | Theorems.Thm_WatsonPseudodeterminism_MASeparation_Supplement_psp_amplification
-- name    : WatsonPseudodeterminism.MASeparation.Supplement.psp_amplification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:30:30.940426+00:00
-- url     : https://prove2.me/theorems/60508d01-fee2-4112-afda-c63b32bb3f97
-- title:
--   §1.1 — Constant-error amplification for psP
-- statement:
--   For every real target error $\varepsilon>0$ there is a natural number $C$, depending only on $\varepsilon$, such that for all input spaces $X,Y$, every two-party partial function $F$ on $X\times Y$ and every natural cost $d$,
--   $$F\text{ has a psP-type protocol of cost }d\ \Longrightarrow\ F\text{ has an }\varepsilon\text{-error psP-type protocol of cost }Cd.$$
--   The amplified protocol is again a single distribution over trees of depth at most $Cd$, its acceptance probability lies in $[0,\varepsilon]\cup[1-\varepsilon,1]$ on **every** input, valid or invalid, and it accepts valid 1-inputs with probability at least $1-\varepsilon$ and valid 0-inputs with probability at most $\varepsilon$.
--
--   This is the psP clause of the paper's amplification remark; §3 uses it to reduce the error of a hypothetical psP protocol from $1/3$ to $0.01$. (The N·BPP clause is a separate item of the base mission.)
--
--   Differences from the source:
--   - generalization: equal-length finite bit-string input spaces → arbitrary types X and Y; reason: finite bit-string spaces are particular types; the amplification statement specializes to them
--   - encoding: any constant > 0 → every real ε > 0, with C depending only on ε; reason: "only affects the cost by a constant factor" is a factor uniform in F and d; ε ≥ 1/3 is the trivial regime and is included
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §1.1, amplification sentence, p. 4 (psP clause; used in §3, p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_Supplement_Models

namespace WatsonPseudodeterminism.MASeparation.Supplement

/-- §1.1, p. 4, psP clause: every positive target error has a cost factor depending on ε only;
the amplified protocol keeps the gap [0, ε] ∪ [1 − ε, 1] on every input. -/
theorem psp_amplification (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℕ, ∀ (X Y : Type) (F : PartialFn X Y) (d : ℕ),
      PsPProtocol F d → PsPProtocolErr ε F (C * d) := by sorry

end WatsonPseudodeterminism.MASeparation.Supplement
