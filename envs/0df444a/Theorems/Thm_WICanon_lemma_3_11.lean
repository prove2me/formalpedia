-- Prove2me | Theorems.Thm_WICanon_lemma_3_11
-- name    : WICanon.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:38.420521+00:00
-- url     : https://prove2.me/theorems/3876f0d5-3304-4f8a-bdd4-d15fe1852c74
-- title:
--   Lemma 3.11 — canonical simulation
-- statement:
--   Let $X^0=(Z,Y^0)$ and $X^1=(Z',Y^1)$ be distributions over $\{0,1\}^{n_0}\times\{0,1\}^n$ with next-bit $\mu$-predictors $\mathrm{Pred}^0,\mathrm{Pred}^1$ and simulators $\mathrm{Sim}^b=\mathrm{Sim}^{\mathrm{Pred}^b}$. If $\mathrm{SD}(X^0,X^1)\le\varepsilon$ then
--
--   $$\Pr_{z\leftarrow Z,\ r\leftarrow(\{0,1\}^\ell)^n}\bigl[\mathrm{Sim}^0(z,r)\ne\mathrm{Sim}^1(z,r)\bigr]\le n\beta+n(n-1)\mu,\qquad\beta=3\varepsilon+4\mu.$$
--
--   This is the paper's main observation: the simulator is canonical, so two statistically close distributions are simulated to the same string on the same coins. It is how witnesses get hidden by a deterministic prover.
--
--   **Formalization Note** $Z$ and $Z'$ may differ, and $z$ comes from the marginal of $X^0$, as printed. Footnote 10 is a hypothesis.
--
--   Differences from the source:
--   - encoding: r ← ({0,1}^ℓ)^n → one tape of n·ℓ bits read in blocks, ℓ = ℓPred + ℓS; reason: same coins
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Lemma 3.11, p.22 (restated as Lemma 3.16, p.27)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QiOPoQ_UPPT
import Definitions.Def_WICanon_Law
import Definitions.Def_WICanon_NextBit

set_option autoImplicit false

namespace WICanon

open QAlgorithms.Complexity QiOPoQ

open Classical in
/-- **Lemma 3.11** (canonical simulation; restated as Lemma 3.16, p.27). Arnon, Mazor, Pass, Silbak,
*Does Witness Indistinguishability Require Cryptography?*, STOC 2027 submission manuscript (sha256
3f78ec3d…), p.22. For `X⁰ = (Z, Y⁰)`, `X¹ = (Z′, Y¹)` over `{0,1}^{n0} × {0,1}^n` with `SD(X⁰, X¹) ≤ ε`
and next-bit `μ`-predictors `Pred⁰`, `Pred¹`,
`Pr_{z←Z, r←({0,1}^ℓ)^n}[Sim⁰(z, r) ≠ Sim¹(z, r)] ≤ n·β + n(n − 1)·μ` for `β = 3ε + 4μ`.

**Formalization Note.** `Z` and `Z′` may differ; `z` is drawn from the marginal of `X⁰`, as printed.
`ℓ = ℓPred + ℓS` is shared, as the two simulators read the same coins. `n − 1` is real subtraction,
so the bound at `n = 0` is `0`. -/
theorem lemma_3_11 (n0 n ℓPred ℓS : ℕ) (X0 X1 : Law) (h0 : IsLawOn X0 (n0 + n))
    (h1 : IsLawOn X1 (n0 + n)) (Pred0 Pred1 : Str → Str → ℚ) (μ ε : ℝ)
    (hP0 : IsNextBitPredictor X0 (n0 + n) ℓPred Pred0 μ)
    (hP1 : IsNextBitPredictor X1 (n0 + n) ℓPred Pred1 μ)
    (hr0 : NoRounding Pred0 ℓPred ℓS) (hr1 : NoRounding Pred1 ℓPred ℓS)
    (hsd : SD X0 X1 ≤ ε) :
    (expect (prefixLaw X0 n0) fun z => avgCoins (n * (ℓPred + ℓS)) fun r =>
      if simBits Pred0 ℓPred ℓS z n r ≠ simBits Pred1 ℓPred ℓS z n r then 1 else 0) ≤
      (n : ℝ) * (3 * ε + 4 * μ) + (n : ℝ) * ((n : ℝ) - 1) * μ := by sorry

end WICanon
