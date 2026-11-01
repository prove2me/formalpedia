-- Prove2me | Theorems.Thm_RecoveringBandits_lemma_3
-- name    : RecoveringBandits.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:55:30.441331+00:00
-- url     : https://prove2.me/theorems/c789b147-2c5d-44e6-a8e0-0c72a940ce0c
-- title:
--   Lemma 3: rounding a supporting frequency to $D[a]$ loses at most a factor $a/(a+1)$
-- statement:
--   Let arm $i$ be admissible, $a\ge1$ and $k\ge1$, and let $x_i=1/d^{(k)}_i$. The rounded period $d_i=\min\{d\ge1/x_i,\ d\in D[a]\}$ of (4) is finite and
--
--   $$\frac{a}{a+1}\,F_i(x_i)\le\frac{R_i(d_i)}{d_i}.$$
--
--   This is Step 1 of the rounding–scheduling framework: replacing the periods by elements of $D[a]$ costs at most a factor $a/(a+1)$ of the long-run reward.
--
--   Differences from the source:
--   - encoding: (R_i(d_i)/d_i) / F_i(x_i) ≥ a/(a+1) → (a/(a+1))·F_i(x_i) ≤ R_i(d_i)/d_i; reason: F_i(x_i) can be 0, where the quotient is undefined; same content where it is defined
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, Lemma 3, p.12

import Mathlib
import Definitions.Def_RecoveringBandits_Admissible
import Definitions.Def_RecoveringBandits_F
import Definitions.Def_RecoveringBandits_supp
import Definitions.Def_RecoveringBandits_roundUp

namespace RecoveringBandits

/-- **Lemma 3**, Simchi-Levi–Zheng–Zhu, arXiv:2106.14813v2, Lemma 3, p.12 (PDF p.12): if
`1/x_i ∈ {d^{(k)}_i}_{k ≥ 1}`, then the rounded period `d_i = min {d ≥ 1/x_i, d ∈ D[a]}` of (4)
satisfies `(R_i(d_i)/d_i) / F_i(x_i) ≥ a/(a+1)`.

**Formalization Note.** The ratio is stated multiplicatively,
`a/(a+1) · F_i(x_i) ≤ R_i(d_i)/d_i`, since `F_i(x_i)` can be `0`. For such `x_i > 0` the
rounded period is finite (`roundUp a x_i = d_i`); `a ≥ 1` as in Step 1. -/
theorem lemma_3 (r : ℕ → ℝ) (Rmax : ℝ) (hr : ArmAdmissible r Rmax) (a : ℕ) (ha : 1 ≤ a)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ n : ℕ, roundUp a (1 / (supp r k : ℝ)) = (n : WithTop ℕ) ∧
      ((a : ℝ) / ((a : ℝ) + 1)) * F r (1 / (supp r k : ℝ)) ≤ r n / (n : ℝ) := by sorry

end RecoveringBandits
