-- Prove2me | Theorems.Thm_SubcubicBA_PlainPKI_lemma_1
-- name    : SubcubicBA.PlainPKI.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:44:00.913725+00:00
-- url     : https://prove2.me/theorems/5f4c4e54-616d-4de4-b36d-78fd73e99013
-- title:
--   Lemma 1 — proofs are sound under accurate votes and accusations
-- statement:
--   Let $B_z$ be a set of at most $t$ byzantine parties among $0,\dots,n-1$, and let every honest party $p$ have an input $x_p\in\{0,1\}$. Suppose the votes cast satisfy voting accuracy (an honest party votes $v\in\{0,1\}$ only if $x_p=v$, and votes $\bot$ only if not all honest inputs are equal) and the accusations made satisfy accusation accuracy (an honest party accuses only byzantine parties). Let $(V,A)$ be a proof for $b\in\{0,1\}$ in the sense of Definition 10, made of cast votes and made accusations. Then
--   $$\neg\big(\forall\text{ honest }p:\ x_p=1-b\big),$$
--   that is, a proof for $b$ cannot exist when all honest parties have input $1-b$ (Definition 5).
--
--   This is the soundness that lets a proof certify that a value may be decided.
--
--   Differences from the source:
--   - reading: Definition 5: computationally infeasible to compute a proof for v if all honest parties have input 1 − v → no proof for b made of cast votes and made accusations exists when all honest inputs are 1 − b; reason: with unforgeable signatures a proof can only consist of votes and accusations actually signed (paper.md reading 1)
--   - encoding: votes and accusations as signed messages → the relations voted p v and accused a c, and finite sets of (party, value) and (accuser, accused) pairs; reason: Lemma 1 is combinatorial; signatures enter only through these relations
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), Lemma 1, p. 13 (with Definitions 5 and 10, pp. 10, 12–13)

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Model
import Definitions.Def_SubcubicBA_PlainPKI_Proofs

namespace SubcubicBA.PlainPKI

/-- Lemma 1 (p. 13). -/
theorem lemma_1 (n t b : ℕ) (hb : b ≤ 1) (Bz : Finset ℕ) (hBz : Bz.card ≤ t)
    (input : ℕ → ℕ) (hinput : ∀ p < n, p ∉ Bz → input p ≤ 1)
    (voted accused : ℕ → ℕ → Prop)
    (hvote : VotingAccurate n Bz input voted) (hacc : AccusationAccurate n Bz accused)
    (V A : Finset (ℕ × ℕ)) (hproof : IsProofSet n t b V A)
    (hV : ∀ x ∈ V, voted x.1 x.2) (hA : ∀ y ∈ A, accused y.1 y.2) :
    ¬ ∀ p < n, p ∉ Bz → input p = 1 - b := by sorry

end SubcubicBA.PlainPKI
