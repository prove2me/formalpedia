-- Prove2me | Theorems.Thm_PctDistortion_lemma_6
-- name    : PctDistortion.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:41:58.186936+00:00
-- url     : https://prove2.me/theorems/75af0b30-f45c-45d8-8391-15ba706c07e5
-- title:
--   Lemma 6 — the stationary mass of state 0 tends to 0 as $r\to\infty$
-- statement:
--   Let $s\ge3$ be an integer and $-1<\hat\nu<1$. For any $\epsilon>0$ there is $R$, depending only on $\hat\nu$, $s$ and $\epsilon$, such that for every $r\ge R$ the stationary probability distribution $p$ of MC (4) with $\ell=sr+1$ satisfies
--   $$p_0\le\epsilon.$$
--
--   Differences from the source:
--   - generalization: ν̂ = ν(G^ABC_H) for H ∈ M_α with ν̂ < 1 − 2/s (so 0 < ν̂ < 1 − 2/s by Proposition 3) → any real ν̂ with −1 < ν̂ < 1; reason: MC (4) depends only on (ν̂, s, r); every ν̂ of the paper lies in (−1, 1), where both transition probabilities are positive
--   - reading: "there exists a sufficiently large r" → ∃ R, ∀ r ≥ R; reason: the proof shows the property for all large r (the quantity tends to its limit); the reading ∃ r alone would be weaker
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 6, p.15 (proof App. E.3, pp.37–38)

import Mathlib
import Definitions.Def_PctDistortion_mcMatrix
import Definitions.Def_MarkovChain

set_option autoImplicit false

namespace PctDistortion

/-- **Lemma 6** (`p₀ → 0`). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 6, p.15 (proof App. E.3, pp.37–38): let `p` be the
stationary probability distribution of MC; then for any `ε > 0` there exists a sufficiently large
`r` (depending only on `ν̂` and `s`) such that `p₀ ≤ ε`.

**Formalization Note.** "Sufficiently large `r`" is read as "for all `r ≥ R`", with `R` chosen
after `ν̂`, `s`, `ε` and before `r`. Stated for every real `ν̂ ∈ (−1, 1)` and integer `s ≥ 3`
(see Lemma 3). -/
theorem lemma_6 (νH : ℝ) (hν₁ : -1 < νH) (hν₂ : νH < 1) (s : ℕ) (hs : 3 ≤ s) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ p : Fin (s * r + 1) → ℝ,
      MarkovChain.IsStationary (mcMatrix νH s r) p → p 0 ≤ ε := by sorry

end PctDistortion
