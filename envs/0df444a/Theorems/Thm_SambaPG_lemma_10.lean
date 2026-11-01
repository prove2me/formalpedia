-- Prove2me | Theorems.Thm_SambaPG_lemma_10
-- name    : SambaPG.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:37:47.865474+00:00
-- url     : https://prove2.me/theorems/3578abf2-c954-4317-a208-0fcbbf9ed06d
-- title:
--   Lemma 10 — the SAMBA update keeps $p$ in the open simplex
-- statement:
--   Let $\alpha\in(0,1)$. Let $p$ be a probability vector with $p_a>0$ for every arm and $\sum_ap_a=1$, let $\ell$ be an arm of maximal probability, let $i$ be any arm and $x\in[0,1]$. Then the SAMBA update $p'$ of (6), with leading arm $\ell$, played arm $i$ and reward $x$, satisfies
--
--   $$
--   p'_a>0\ \text{ for every arm }a,\qquad \sum_ap'_a=1 .
--   $$
--
--   So the SAMBA process never leaves the open probability simplex.
--
--   Differences from the source:
--
--   - reading: the update (6) uses the leading arm a⋆(t) = argmax p(t) and the algorithm’s α ∈ (0, 1) (p.4) → hypotheses: ℓ maximizes p; 0 < α < 1; reason: the lemma is false for α ≥ 1 (two tied arms, the non-leader rewarded)
--   - generalization: Bernoulli reward R_a(t) ∈ {0, 1} → any reward x ∈ [0, 1]; reason: contains {0, 1}; the proof uses only 0 ≤ R ≤ 1
--   - encoding: indicator I_a(t) of the played arm → a played arm i with I_a = [a = i]; reason: exactly one arm is played
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, Lemma 10, p.26 (proof §A.7, p.26)

import Mathlib
import Definitions.Def_SambaPG_sambaStep

namespace SambaPG

/-- **Lemma 10 (the SAMBA update stays in the open simplex).**
Denisov & Walton, *Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits*,
arXiv:2007.10229v3, Lemma 10, p.26 (proof §A.7, p.26); also §3.4, p.7.

If `p` has positive entries summing to `1`, `ℓ` is an arm of maximal probability (the leading arm),
`i` is the arm played and `x ∈ [0, 1]` its reward, then the updated vector `sambaStep α p ℓ i x` of
(6) again has positive entries summing to `1`, for every learning rate `α ∈ (0, 1)`.

**Formalization Note.** `α ∈ (0, 1)` is the standing assumption of the algorithm box (p.4: "For
`α ∈ (0, 1)`, these probabilities remain in the probability simplex"); the lemma is false for
`α ≥ 1`. The reward is any `x ∈ [0, 1]`, which covers the Bernoulli rewards `x ∈ {0, 1}`. -/
theorem lemma_10 {A : Type*} [Fintype A] [DecidableEq A] {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {p : A → ℝ} (hpos : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1) {ℓ : A} (hℓ : ∀ a, p a ≤ p ℓ)
    (i : A) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∀ a, 0 < sambaStep α p ℓ i x a) ∧ ∑ a, sambaStep α p ℓ i x a = 1 := by sorry

end SambaPG
