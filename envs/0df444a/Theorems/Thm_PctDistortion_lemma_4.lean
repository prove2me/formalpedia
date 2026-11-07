-- Prove2me | Theorems.Thm_PctDistortion_lemma_4
-- name    : PctDistortion.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:25.511203+00:00
-- url     : https://prove2.me/theorems/2a1e114e-2dc7-4fdc-afc4-25a33a727d86
-- title:
--   Lemma 4 — the unique equilibrium of the reduced game is the stationary distribution of MC and its reflection
-- statement:
--   Let $s\ge3$ and $r\ge1$ be integers, $\ell=sr+1$, and let MC be the Markov chain (4) on $\{0,\dots,\ell-1\}$ with parameter $\hat\nu$, $-1<\hat\nu<1$.
--   Let $p$ be the stationary distribution of MC. The reduced game on $C$ with payoff (3) has a unique equilibrium $(a,b)$: $a=p$, and $b$ is the reflection of $a$ about $0$, $b_0=a_0$ and $b_i=a_{\ell-i}$ for $i\in\{1,\dots,\ell-1\}$. Both players assign strictly positive probability to every $i$: $a_i>0$ and $b_i>0$.
--
--   Differences from the source:
--   - generalization: ν̂ = ν(G^ABC_H) for H ∈ M_α with ν̂ < 1 − 2/s (so 0 < ν̂ < 1 − 2/s by Proposition 3) → any real ν̂ with −1 < ν̂ < 1; reason: MC (4) depends only on (ν̂, s, r); every ν̂ of the paper lies in (−1, 1), where both transition probabilities are positive
--   - encoding: "has a unique equilibrium (a, b) … a = p … b the reflection" → (a, b) is an equilibrium iff a = p and b = reflect p; reason: existence and uniqueness in one statement
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 4, p.14 (proof App. E.2, pp.36–37)

import Mathlib
import Definitions.Def_PctDistortion_mcMatrix
import Definitions.Def_PctDistortion_reducedPayoff
import Definitions.Def_MarkovChain
import Definitions.Def_BlottoLP_Flow_ZeroSum

set_option autoImplicit false

namespace PctDistortion

/-- **Lemma 4** (the unique equilibrium of the reduced game). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 4, p.14 (proof App. E.2,
pp.36–37): the reduced game on `C` (payoff (3)) has a unique equilibrium `(a, b)`: `a = p` is the
stationary probability distribution of MC, and `b` is the reflection of `a` about `0`
(`b₀ = a₀`, `b_i = a_{ℓ−i}`); both assign strictly positive probability to every
`i ∈ {0, …, ℓ − 1}`.

**Formalization Note.** Stated for every real `ν̂ ∈ (−1, 1)` and integers `s ≥ 3`, `r ≥ 1` (see
Lemma 3). The equivalence "`(a, b)` is an equilibrium iff `a = p` and `b` is its reflection" is
existence and uniqueness together. -/
theorem lemma_4 (νH : ℝ) (hν₁ : -1 < νH) (hν₂ : νH < 1) (s r : ℕ) (hs : 3 ≤ s) (hr : 1 ≤ r) (p : Fin (s * r + 1) → ℝ)
    (hp : MarkovChain.IsStationary (mcMatrix νH s r) p) :
    (∀ a b : Fin (s * r + 1) → ℝ,
      BlottoLP.Flow.IsNashEq (reducedPayoff νH s r) a b ↔ a = p ∧ b = reflect p) ∧
      ∀ i, 0 < p i ∧ 0 < reflect p i := by sorry

end PctDistortion
