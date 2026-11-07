-- Prove2me | Theorems.Thm_PrivLittlestone_lemma_2_3
-- name    : PrivLittlestone.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:36:44.203613+00:00
-- url     : https://prove2.me/theorems/844ff8dc-00c3-4e1b-9392-d814e44beded
-- title:
--   Lemma 2.3 — structural sampling is $(2\eta,\tau)$-private, and $(4\eta,(1+e^{2\eta})\tau)$-private for one deletion and one insertion
-- statement:
--   Let a ranked candidate system of height $D$ and branching parameter $B \ge 1$ be given, with candidate distributions $Q_S$ from (2). If
--   $$
--   0 < 2\eta \le 1, \qquad 0 < \tau < 1, \qquad a = \eta + \log\frac{8B}{\tau},
--   $$
--   then a draw from $Q_S$ is $(2\eta, \tau)$-private under insertion/deletion: for every ordered pair $(S, S')$ of insertion/deletion neighbors and every set $E$ of candidates,
--   $$
--   Q_S(E) \le e^{2\eta} Q_{S'}(E) + \tau .
--   $$
--   Moreover, if $S''$ arises from $S$ by at most one deletion and one insertion, then
--   $$
--   Q_S(E) \le e^{4\eta} Q_{S''}(E) + (1 + e^{2\eta})\tau .
--   $$
--
--   This is the structural exponential mechanism of Moran and Yan with score $-\ell_S$ and sensitivity one; it is the privacy guarantee of every candidate release of the continual learner.
--
--   Differences from the source:
--
--   - encoding: every event E of the draw → every set E ⊆ U, with Q_S(E) a finite sum over C(S); reason: Q_S has finite support; same values
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Lemma 2.3, p.5 (proof in Appendix A.1, p.17)

import Mathlib
import Definitions.Def_PrivLittlestone_gibbsProb
import Definitions.Def_PrivLittlestone_AtMostOneDelIns

namespace PrivLittlestone

/-- **Lemma 2.3 (Static structural sampling; [MY26])** (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
Lemma 2.3, p.5; proof in Appendix A.1, p.17). For a ranked candidate system, if `0 < 2η ≤ 1`,
`0 < τ < 1` and `a = η + log(8B/τ)`, then a draw from `Q_S` is `(2η, τ)`-private under
insertion/deletion: `Q_S(E) ≤ e^{2η} Q_{S'}(E) + τ` for every ordered neighbor pair and every
`E ⊆ U`; and a change of at most one deletion and one insertion gives `(4η, (1 + e^{2η})τ)`-privacy. -/
theorem lemma_2_3 {Z U : Type*} {D : ℕ} {B : ℝ} (sys : RankedCandidateSystem Z U D B)
    (η τ a : ℝ) (hη : 0 < 2 * η) (hη1 : 2 * η ≤ 1) (hτ : 0 < τ) (hτ1 : τ < 1)
    (ha : a = η + Real.log (8 * B / τ)) :
    (∀ S S' : List Z, IsInsDelNeighbor S S' → ∀ E : Set U,
      gibbsProb sys η a S E ≤ Real.exp (2 * η) * gibbsProb sys η a S' E + τ) ∧
    (∀ S S'' : List Z, AtMostOneDelIns S S'' → ∀ E : Set U,
      gibbsProb sys η a S E ≤
        Real.exp (4 * η) * gibbsProb sys η a S'' E + (1 + Real.exp (2 * η)) * τ) := by sorry

end PrivLittlestone
