-- Prove2me | Theorems.Thm_SubcubicBA_PlainPKI_lemma_7
-- name    : SubcubicBA.PlainPKI.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:43:04.830996+00:00
-- url     : https://prove2.me/theorems/b19cfc18-be94-44b9-aa5b-f5a767441f31
-- title:
--   Lemma 7 — disperser forwarding loses at most n/20 votes
-- statement:
--   Let $G_1$ be an $(n/20,\,7n/10)$-disperser on the parties. A party $p$ forwards the vote of each party $s$ in a set $S$ of votes from distinct parties to the out-neighbours $N_{G_1}(s)$, so party $q$ receives $E_q=\{s\in S: q\in N_{G_1}(s)\}$ in the first round of SpreadVotes. Then every set $H$ of at least $4n/10$ parties satisfies
--   $$\Big|\bigcup_{q\in H}E_q\Big|\ge|S|-\frac n{20}.$$
--
--   Any $4n/10$ parties therefore jointly hold almost all of $p$'s votes, which is what allows them to form proofs in Lemma 8.
--
--   Differences from the source:
--   - generalization: G₁, the (n/20, 7n/10)-disperser of SpreadVotes (Theorem 11) → an arbitrary (n/20, 7n/10)-disperser; reason: the proof uses only the disperser property; Theorem 11's graph is a special case
--   - encoding: votes from distinct parties; E_q the votes of S that q received after the first round → S a set of parties; E_q = {s ∈ S : q ∈ N_{G₁}(s)}; reason: SpreadVotes sends the vote of s to N_{G₁}(s); the source identifies votes with their voters
--   - encoding: |H| ≥ 4n/10 and |S| − n/20 → real-valued thresholds; reason: same instances
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), Lemma 7, p. 18

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Graphs

namespace SubcubicBA.PlainPKI

/-- Lemma 7 (p. 18). The vote of party `s ∈ S` is forwarded by `p` to `N_{G₁}(s)`, so party `q`
receives the votes `E_q = {s ∈ S : q ∈ N_{G₁}(s)}` in the first round of SpreadVotes. -/
theorem lemma_7 (n : ℕ) (G₁ : Fin n → Finset (Fin n))
    (hG₁ : IsDisperser G₁ ((n : ℝ) / 20) (7 * (n : ℝ) / 10)) (S H : Finset (Fin n))
    (hH : 4 * (n : ℝ) / 10 ≤ (H.card : ℝ)) :
    (S.card : ℝ) - (n : ℝ) / 20 ≤
      ((H.biUnion fun q => S.filter fun s => q ∈ G₁ s).card : ℝ) := by sorry

end SubcubicBA.PlainPKI
