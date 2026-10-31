-- Prove2me | Theorems.Thm_WeightedCoordGames_claim_1
-- name    : WeightedCoordGames.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:29.059517+00:00
-- url     : https://prove2.me/theorems/e4c940b4-6106-4389-9ead-418441b34380
-- title:
--   Claim 1 (Appendix) — a sufficient condition for $\mu(s)<_{\mathrm{lex}}\mu(s')$
-- statement:
--   Consider a coordination game on an open chain with non-empty colour sets, and let $s$ and $s'$ be two joint strategies such that
--   $$
--   \mu(s)=(\mathrm{guard}(s),0,|\mathrm{prefix}(s)|,-\mathrm{NBR}(s)),\qquad \mathrm{guard}(s)\le\mathrm{guard}(s'),\qquad |\mathrm{prefix}(s)|<|\mathrm{prefix}(s')|.
--   $$
--   Then $\mu(s)<_{\mathrm{lex}}\mu(s')$.
--
--   The claim is the step of the analysis of Algorithm 1 (Lemma 14) that handles rounds lengthening the prefix without lowering the guard.
--
--   Differences from the source:
--   - encoding: quadruples ordered by $<_{\mathrm{lex}}$ → `Lex (ℕ × Lex (ℕ × Lex (ℕ × ℤ)))`; reason: the same order on the same quadruples
-- source:
--   Apt–Simon–Wojtczak, Coordination Games on Weighted Directed Graphs, arXiv:1910.02693v2 (preprint), Appendix, Claim 1, p.37 (proof p.38)

import Mathlib
import Definitions.Def_WeightedCoordGames_Model
import Definitions.Def_WeightedCoordGames_Algorithm

namespace WeightedCoordGames

/-- **Claim 1** (Apt–Simon–Wojtczak, arXiv:1910.02693v2, Appendix, p.37; proof p.38). Let `s` and
`s'` be two joint strategies such that `µ(s) = (guard(s), 0, |prefix(s)|, −NBR(s))`,
`guard(s) ≤ guard(s')` and `|prefix(s)| < |prefix(s')|`. Then `µ(s) <lex µ(s')`. -/
theorem claim_1 {V M : Type*} [Fintype V] [DecidableEq V] [Fintype M] [DecidableEq M]
    {m v : ℕ} (O : OpenChain V m v) (C : V → Finset M) (hC : ∀ u, (C u).Nonempty)
    (s s' : V → M) (hs : (chainGame O C).toGame.IsJoint s)
    (hs' : (chainGame O C).toGame.IsJoint s')
    (hmu : O.mu C s = toLex (O.guard C s, toLex (0, toLex (O.prefixLen C s, -(O.nbr C s : ℤ)))))
    (hg : O.guard C s ≤ O.guard C s') (hp : O.prefixLen C s < O.prefixLen C s') :
    O.mu C s < O.mu C s' := by sorry

end WeightedCoordGames
