-- Prove2me | Theorems.Thm_PrivLittlestone_lemma_3_3
-- name    : PrivLittlestone.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:38:03.57081+00:00
-- url     : https://prove2.me/theorems/bc34b2bc-a901-45e5-8325-00682280c040
-- title:
--   Lemma 3.3 — a mistaken phase contracts the potential: $Z_{SA} \le \frac{9}{10}Z_S$
-- statement:
--   Let a ranked candidate system of height $D$ and branching parameter $B$ be given, and let $\eta, a > 0$ and $T \in \mathbb N$. Let $A = (u_1, \dots, u_b)$ be a block of records with $b \le T$ and
--   $$
--   \mathbb E_{h \sim Q_S}\, \ell_{u_i}(h) \ge \tfrac13 \quad \text{for every } i .
--   $$
--   If $\eta b \ge 12$ and $\gamma T \le 1/200$, then $Z_{SA} \le \tfrac{9}{10} Z_S$.
--
--   This turns a long enough batch of certified mistakes into a constant-factor decrease of the potential, which bounds the number of phases.
--
--   Differences from the source: none.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Lemma 3.3, p.6

import Mathlib
import Definitions.Def_PrivLittlestone_gibbsExp
import Definitions.Def_PrivLittlestone_gammaTerm

namespace PrivLittlestone

/-- **Lemma 3.3 (A mistaken phase contracts the potential)** (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256
21480556…c562), Lemma 3.3, p.6). For a ranked candidate system and `η, a > 0`, let
`A = (u_1, …, u_b)` with `b ≤ T` and `E_{h∼Q_S} ℓ_{u_i}(h) ≥ 1/3` for every `i`. If `ηb ≥ 12` and
`γT ≤ 1/200`, then `Z_{SA} ≤ (9/10) Z_S`. -/
theorem lemma_3_3 {Z U : Type*} {D : ℕ} {B : ℝ} (sys : RankedCandidateSystem Z U D B)
    (η a : ℝ) (hη : 0 < η) (ha : 0 < a) (T : ℕ) (S A : List Z) (hb : A.length ≤ T)
    (hA : ∀ u ∈ A, (1 : ℝ) / 3 ≤ gibbsExp sys η a S (fun h => (sys.loss u h : ℝ)))
    (hηb : 12 ≤ η * (A.length : ℝ)) (hγ : gammaTerm η a B D * (T : ℝ) ≤ 1 / 200) :
    potential sys η a (S ++ A) ≤ 9 / 10 * potential sys η a S := by sorry

end PrivLittlestone
