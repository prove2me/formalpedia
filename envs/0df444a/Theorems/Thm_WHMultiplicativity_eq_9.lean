-- Prove2me | Theorems.Thm_WHMultiplicativity_eq_9
-- name    : WHMultiplicativity.eq_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:25:30.014816+00:00
-- url     : https://prove2.me/theorems/396fc080-eb8d-42d1-8129-86c120c367f3
-- title:
--   Eq. (9): $\nu_p(S) = (d-1)^{-(1-1/p)}$
-- statement:
--   Let $d\ge 2$ and let $S$ be the Werner–Holevo channel on $d\times d$ matrices. For every real $p > 1$ the set of output norms $\{\|S(\rho)\|_p\}$ over density matrices $\rho$ is bounded above and
--
--   $$
--   \nu_p(S) = (d-1)^{-(1-1/p)} .
--   $$
--
--   Moreover, for $p = \infty$ (operator norm) the set is bounded above and $\nu_\infty(S) = (d-1)^{-1}$.
--
--   This is the single-channel side of the multiplicativity conjecture.
--
--   Differences from the source:
--   - generalization: ν_p(S) = (d − 1)^{−(1−1/p)} for 1 < p < ∞ → also ν_∞(S) = (d − 1)^{−1}; reason: the limit case p = ∞ of (9), used by the page after (13) for Δ(∞, Φm) = log(4/3); the finite-p clause is the page's statement
--   - generalization: ν_p(S) as a supremum → additional conclusions BddAbove (outputNorms p S); reason: extra conclusions that make the supremum a genuine one
--   - encoding: ν_p(S) = sup over all input density operators of ‖S(ρ)‖_p → maxOutputNorm p S, the real sSup of outputNorms p S over every density matrix; reason: same supremum; the BddAbove clauses rule out Lean's junk value of sSup
--   - encoding: ‖X‖_p = (tr|X|^p)^{1/p} for real p, and ‖·‖_∞ the operator norm → schattenNorm p X with p : ℝ≥0∞, a real p entering as ENNReal.ofReal p and ∞ as ⊤; reason: tr|X|^p = tr (XᴴX)^{p/2}; ⊤ gives the ℓ² operator norm; same values
--   - encoding: d × d matrices with denominator d − 1 (d ≥ 2 implicit) → hypothesis 2 ≤ d; reason: excludes only d = 1, where the page's formula divides by zero
-- source:
--   Werner and Holevo, Counterexample to an additivity conjecture for output purity of quantum channels, arXiv:quant-ph/0203003v1, eq. (9), p.2 (p = ∞ value as used after eq. (13))

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_WHMultiplicativity_outputNorms
import Definitions.Def_WHMultiplicativity_maxOutputNorm

open scoped ENNReal
open WHAdditivity.Renyi

namespace WHMultiplicativity

/-- Werner and Holevo, arXiv:quant-ph/0203003v1, eq. (9), p.2: the maximal output `p`-norm of the
channel `S` on `d × d` matrices is `ν_p(S) = (d − 1)^{−(1−1/p)}` for `1 < p < ∞`; and (the
`p = ∞` case used after eq. (13)) `ν_∞(S) = (d − 1)^{−1}`.

**Formalization Note.** `ν_p = maxOutputNorm`, the real supremum of `‖S(ρ)‖_p` over all density
matrices `ρ`; each clause also asserts that this set is bounded above, so the supremum is not
Lean's junk value. A real `p` enters as `ENNReal.ofReal p`; `p = ∞` is `⊤` (operator norm).
`2 ≤ d` is the paper's standing assumption. -/
theorem eq_9 (d : ℕ) (hd : 2 ≤ d) :
    (∀ p : ℝ, 1 < p →
        BddAbove (outputNorms (ENNReal.ofReal p) (wernerHolevo d)) ∧
          maxOutputNorm (ENNReal.ofReal p) (wernerHolevo d) = ((d : ℝ) - 1) ^ (-(1 - 1 / p))) ∧
      (BddAbove (outputNorms ⊤ (wernerHolevo d)) ∧
          maxOutputNorm ⊤ (wernerHolevo d) = ((d : ℝ) - 1)⁻¹) := by sorry

end WHMultiplicativity
