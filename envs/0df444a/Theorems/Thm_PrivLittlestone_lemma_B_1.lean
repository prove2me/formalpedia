-- Prove2me | Theorems.Thm_PrivLittlestone_lemma_B_1
-- name    : PrivLittlestone.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:37:29.997209+00:00
-- url     : https://prove2.me/theorems/0ad6b619-bf9d-44f3-9823-da7032f04df7
-- title:
--   Lemma B.1 — retained sequences in the two worlds differ by one deletion and one insertion; candidate releases are $(\varepsilon_s, 3\tau)$-private
-- statement:
--   Fix an adaptive single-challenge adversary with its random coins and a common public history at a candidate-release step, given by the released classifiers $g_1, g_2, \dots$ (whether or not it has positive probability in either world). Replaying the adversary and the deterministic retention filter $\kappa$ in the two challenge worlds, through any round, produces retained sequences $S^0, S^1$ that differ by at most one deletion and one insertion (in both orders).
--
--   Consequently, with the parameters (4)–(6), for $K, m, T \ge 1$, $0 < \varepsilon \le 1$ and $0 < \delta \le 1/2$, each fresh candidate-release kernel is $(\varepsilon_s, 3\tau)$-private for the hidden bit: for every set $E$ of candidates,
--   $$
--   Q_{S^0}(E) \le e^{\varepsilon_s} Q_{S^1}(E) + 3\tau, \qquad Q_{S^1}(E) \le e^{\varepsilon_s} Q_{S^0}(E) + 3\tau .
--   $$
--
--   Differences from the source:
--
--   - encoding: fixed adversary coins and a common augmented transcript prefix → a deterministic single-challenge strategy and an arbitrary sequence of released classifiers, replayed through any round t; reason: with the coins fixed the replay depends on the history only through the public classifiers; arbitrary sequences include the zero-probability histories
--   - reading: each candidate-release kernel is (ε_s, 3τ)-private → the inequality for the parameters (4)–(6) under K, m, T ≥ 1, 0 < ε ≤ 1, 0 < δ ≤ 1/2; reason: the constant 3τ rests on 1 + e^{2η} < 3, which the paper states under these parameters
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Lemma B.1, p.21

import Mathlib
import Definitions.Def_PrivLittlestone_retainedSeq
import Definitions.Def_PrivLittlestone_worldInput
import Definitions.Def_PrivLittlestone_IsSingleChallenge
import Definitions.Def_PrivLittlestone_AtMostOneDelIns
import Definitions.Def_PrivLittlestone_gibbsProb
import Definitions.Def_PrivLittlestone_aP

namespace PrivLittlestone

/-- **Lemma B.1 (Filtered histories)** (He–He, *Private Online Learning of Littlestone Classes and
Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), Lemma B.1, p.21). Fix a
single-challenge adversary strategy (its coins fixed) and a common public history, i.e. any
sequence of released classifiers `g_0, …, g_{T−1}` (reachable or not). Replaying the adversary and
the deterministic retention filter `κ` through any round `t` in the two challenge worlds produces
retained sequences `S⁰, S¹` differing by at most one deletion and one insertion (in either order of
the worlds). Thus, with the parameters (4)–(6) (`K, m, T ≥ 1`, `0 < ε ≤ 1`, `0 < δ ≤ 1/2`), each
fresh candidate-release kernel `Q_{S^b}` is `(ε_s, 3τ)`-private for the hidden bit:
`Q_{S⁰}(E) ≤ e^{ε_s} Q_{S¹}(E) + 3τ` and `Q_{S¹}(E) ≤ e^{ε_s} Q_{S⁰}(E) + 3τ` for every `E ⊆ U`.

**Formalization Note** "Histories whose probability is zero in one world" are covered because
`gs` is arbitrary; the kernel is a draw from `Q_S` (finite support). -/
theorem lemma_B_1 {X Z U : Type*} {D : ℕ} {B : ℝ} {T : ℕ} (sys : RankedCandidateSystem Z U D B)
    (κ : (X → Bool) → X × Bool → Option Z) (adv : Adversary X T) (hadv : IsSingleChallenge adv)
    (gs : Fin T → X → Bool) (t : ℕ) :
    AtMostOneDelIns
        (retainedSeq κ gs (fun i => worldInput adv false i (fun k => gs (Fin.castLE i.isLt k))) t)
        (retainedSeq κ gs (fun i => worldInput adv true i (fun k => gs (Fin.castLE i.isLt k))) t) ∧
      AtMostOneDelIns
        (retainedSeq κ gs (fun i => worldInput adv true i (fun k => gs (Fin.castLE i.isLt k))) t)
        (retainedSeq κ gs (fun i => worldInput adv false i (fun k => gs (Fin.castLE i.isLt k))) t) ∧
      ∀ (K m : ℕ) (ε δ : ℝ), 1 ≤ K → 1 ≤ m → 1 ≤ T → 0 < ε → ε ≤ 1 → 0 < δ → δ ≤ 1 / 2 →
        ∀ E : Set U,
          gibbsProb sys (etaP K m ε δ) (aP K m T B ε δ)
              (retainedSeq κ gs (fun i => worldInput adv false i (fun k => gs (Fin.castLE i.isLt k))) t) E ≤
            Real.exp (epsS K m ε δ) * gibbsProb sys (etaP K m ε δ) (aP K m T B ε δ)
              (retainedSeq κ gs (fun i => worldInput adv true i (fun k => gs (Fin.castLE i.isLt k))) t) E +
              3 * tauP K m T δ ∧
          gibbsProb sys (etaP K m ε δ) (aP K m T B ε δ)
              (retainedSeq κ gs (fun i => worldInput adv true i (fun k => gs (Fin.castLE i.isLt k))) t) E ≤
            Real.exp (epsS K m ε δ) * gibbsProb sys (etaP K m ε δ) (aP K m T B ε δ)
              (retainedSeq κ gs (fun i => worldInput adv false i (fun k => gs (Fin.castLE i.isLt k))) t) E +
              3 * tauP K m T δ := by sorry

end PrivLittlestone
