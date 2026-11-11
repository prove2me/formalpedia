-- Prove2me | Theorems.Thm_SpacePropTest_lemma_28
-- name    : SpacePropTest.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:51.636714+00:00
-- url     : https://prove2.me/theorems/629a98f5-8302-4de3-b87f-f939757a306d
-- title:
--   Lemma 28, p.25 — a $2^{O(L\log(n/\varepsilon))}$-state clock-equipped estimator of $\Pr_{i,x}[D_if_\rho^{\le L}(x)\le t]$ between the thresholds $-1/(2n)$ and $-1/(4n)$, error $\varepsilon/(16n^3)$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $n\ge1$, $\varepsilon\in(0,1]$ and $\rho,L$ as in (5). There is a clock-equipped estimator with at most $2^{CL\log_2(2n/\varepsilon)}$ states that makes at most $C\,(n^L/\varepsilon)^C$ queries and, for every $f:\{\pm1\}^n\to\{\pm1\}$, outputs $\hat\gamma$ with probability at least $5/6$ satisfying
--
--   $$\Pr_{i,x}\Big[D_if_\rho^{\le L}(x)\le-\frac1{2n}\Big]-\frac{\varepsilon}{16n^3}\le\hat\gamma\le\Pr_{i,x}\Big[D_if_\rho^{\le L}(x)\le-\frac1{4n}\Big]+\frac{\varepsilon}{16n^3}.$$
--
--   This is the second test of the monotonicity tester.
--
--   Differences from the source:
--   - encoding: $f:\{\pm1\}^n\to\{\pm1\}$ on $\{\pm1\}^n$ → a Boolean function on $\{0,1\}^n$ (`Fin n → Bool`) read through $\mathrm{false}\mapsto-1$, $\mathrm{true}\mapsto+1$; reason: order-preserving bijection; the same monotone functions, derivatives and Fourier coefficients
--   - encoding: $\Pr_{x\sim\{\pm1\}^n,\,i\sim[n]}[\cdot]$ → the fraction of pairs $(x,i)\in\{0,1\}^n\times[n]$ satisfying the event; reason: $x$ and $i$ are uniform and independent
--   - generalization: $L:=O(\sqrt n\log(n/\varepsilon)/\varepsilon^2)$ such that $\rho\le1-3\log(n/\varepsilon)/L$ (5) → every positive integer $L$ with $\rho\le1-3\ln(n/\varepsilon)/L$; reason: every $L$ the paper allows satisfies this condition, so the statement specializes to the paper's $L$
--   - reading: clock-equipped algorithm (informal, pp.2–4, 17; formal definition deferred to [CCP+26]) → a $T$-step algorithm with time-indexed query and next-state distributions, a start state, and an output read off the state at time $T$; $S$ states means at most $S$ states, after $K$ queries means $T\le K$; reason: minimal reading of pp.2–4 and 17 (paper.md decision 6); the clock is not counted among the states, as in the paper's conversion to $O(ST)$ states
--   - reading: $2^{O(L\log(n/\varepsilon))}$ states, $\mathrm{poly}(n^L,1/\varepsilon)$ queries → at most $2^{CL\log_2(2n/\varepsilon)}$ states and $C\,(n^L/\varepsilon)^C$ queries, $C$ absolute and chosen before $n,\varepsilon,L$; the algorithm is chosen before $f$; reason: standard readings of $O(\cdot)$ and $\mathrm{poly}$; the bound $(n^L/\varepsilon)^C$ without the factor $C$ would allow a single query at $n=1$, $\varepsilon=1$, where the claim fails
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Lemma 28, p.25 (PDF 27)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_Fourier
import Definitions.Def_SpacePropTest_ClockAlg

set_option autoImplicit false

namespace SpacePropTest

/-- **Lemma 28 (Estimating `Pr_{i,x}[D_i f_ρ^{≤L}(x) ≤ t]`)** (C. Canonne, X. Chen, W. Pires,
T. Pitassi, R. A. Servedio, *The Space Complexity of Property Testing*, manuscript of November 2,
2026, sha256 65850aa6…; p.25 (PDF 27)). There is a `2^{O(L log(n/ε))}`-state clock-equipped
algorithm which, after `poly(n^L, 1/ε)` queries, outputs `γ̂` with
`Pr_{i,x}[D_i f_ρ^{≤L}(x) ≤ −1/(2n)] − ε/(16n³) ≤ γ̂ ≤ Pr_{i,x}[D_i f_ρ^{≤L}(x) ≤ −1/(4n)] + ε/(16n³)`
with probability at least `5/6`, for every `f`.

**Formalization Note.** `C` is absolute and chosen before `n, ε, L`; the algorithm before `f`.
`log(n/ε)` in the exponent is `log₂(2n/ε)`; `poly(n^L, 1/ε)` is `C·(n^L/ε)^C`. -/
theorem lemma_28 : ∃ C : ℝ, ∀ (n : ℕ), 1 ≤ n → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ (L : ℕ),
    IsLParam n ε L →
    ∃ (σ : Type) (_ : Fintype σ) (_ : DecidableEq σ) (E : ClockEstimator n σ),
      (Fintype.card σ : ℝ) ≤ 2 ^ (C * L * Real.logb 2 (2 * n / ε)) ∧
      (E.T : ℝ) ≤ C * ((n : ℝ) ^ L / ε) ^ C ∧
      ∀ f : BoolFn n,
        5 / 6 ≤ E.probWithin f
          (edgeProbLe (trunc L (noiseOp (rho n ε) (pmFn f))) (-1 / (2 * n)) -
            ε / (16 * (n : ℝ) ^ 3))
          (edgeProbLe (trunc L (noiseOp (rho n ε) (pmFn f))) (-1 / (4 * n)) +
            ε / (16 * (n : ℝ) ^ 3)) := by sorry

end SpacePropTest
