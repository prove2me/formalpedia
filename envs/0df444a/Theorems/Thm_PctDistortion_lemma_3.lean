-- Prove2me | Theorems.Thm_PctDistortion_lemma_3
-- name    : PctDistortion.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:41:59.043907+00:00
-- url     : https://prove2.me/theorems/55e2c87f-baaa-4503-90fb-15e9df992928
-- title:
--   Lemma 3 — MC is irreducible and aperiodic with a unique, positive stationary distribution
-- statement:
--   Let $s\ge3$ and $r\ge1$ be integers, $\ell=sr+1$, and let MC be the Markov chain (4) on $\{0,\dots,\ell-1\}$ with parameter $\hat\nu$, $-1<\hat\nu<1$.
--   Then MC is irreducible and aperiodic, and hence has a unique stationary probability distribution $p$, and $p$ has strictly positive entries.
--
--   Differences from the source:
--   - generalization: ν̂ = ν(G^ABC_H) for H ∈ M_α with ν̂ < 1 − 2/s (so 0 < ν̂ < 1 − 2/s by Proposition 3) → any real ν̂ with −1 < ν̂ < 1; reason: MC (4) depends only on (ν̂, s, r); every ν̂ of the paper lies in (−1, 1), where both transition probabilities are positive
--   - encoding: irreducible, aperiodic → reachability by matrix powers; period 1 as "the only common divisor of all return times is 1"; reason: the textbook definitions for a finite chain
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 3, p.14 (proof App. E.2, p.36)

import Mathlib
import Definitions.Def_PctDistortion_mcMatrix
import Definitions.Def_MarkovChain

set_option autoImplicit false

namespace PctDistortion

/-- **Lemma 3** (ergodicity of MC). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 3, p.14 (proof App. E.2, p.36): the Markov chain
MC (4) on `{0, …, ℓ − 1}`, `ℓ = s r + 1`, is irreducible and aperiodic, and hence has a unique
stationary probability distribution `p`, with strictly positive entries.

**Formalization Note.** MC depends only on `(ν̂, s, r)`; it is stated for every real `ν̂` with
`−1 < ν̂ < 1` (both transition probabilities of (4) positive), which contains the paper's
`ν̂ = ν(G^ABC_H) ∈ (0, 1 − 2/s)`, and for integers `s ≥ 3`, `r ≥ 1` (§4.1). Stationarity is
`MarkovChain.IsStationary` (`p ∈ Δ`, `p M = p`). -/
theorem lemma_3 (νH : ℝ) (hν₁ : -1 < νH) (hν₂ : νH < 1) (s r : ℕ) (hs : 3 ≤ s) (hr : 1 ≤ r) :
    IsIrreducible (mcMatrix νH s r) ∧ IsAperiodic (mcMatrix νH s r) ∧
      (∃! p, MarkovChain.IsStationary (mcMatrix νH s r) p) ∧
      ∀ p, MarkovChain.IsStationary (mcMatrix νH s r) p → ∀ i, 0 < p i := by sorry

end PctDistortion
