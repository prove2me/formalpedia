-- Prove2me | Theorems.Thm_ValTrackRM_Public_Supplement_theorem_5
-- name    : ValTrackRM.Public.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:05:12.234406+00:00
-- url     : https://prove2.me/theorems/e5bd257e-21a0-4691-a1a9-fae66fbbc453
-- title:
--   Theorem 5 — sampling guarantee and polynomial runtime
-- statement:
--   Let $m,k\ge1$, let $0=r^{(0)}<r^{(1)}<\cdots<r^{(m)}$, and let the $T$ customer valuations have any independent grid distributions. For every real $\varepsilon>0$, choose exactly
--   $$C=\left\lceil\frac{6}{e\pi^2\varepsilon}\right\rceil.$$
--   Algorithm 2, implemented with the least-index minimum-level selector, satisfies
--   $$\mathbb E[\mathrm{ALG}^{\mathrm{Samp}}]\ge (1/q-\varepsilon)\mathbb E[\mathrm{OPT}].$$
--   It also runs in deterministic polynomial time in $1/\varepsilon,k,T,m$ in the paper's arithmetic and categorical-sampling oracle model. The statement gives both an actual simulated-transition bound $C(k+1)T^4$ and an operation bound on every execution branch:
--   $$1000\left(2+\frac{6}{e\pi^2\varepsilon}\right)(k+1)^2(m+1)^3(T+1)^4.$$
--   Initialization, input storage, minimum-level and price-table scans, failed trials, price selection and public observations are counted. It additionally asserts that the implemented selector is minimal and that $1\le C\le1+6/(e\pi^2\varepsilon)$.
--
--   This is the full guarantee with the printed sampling constant and no upper restriction on $\varepsilon$.
--
--   **Formalization Note** The ec14 summation inference is arithmetically invalid with the printed $C$. The statement preserves that constant and the competitive conclusion; the sharper first-failure estimate recorded in MODERATION_NOTES.md and DISPROOF.md supplies a supported repair of the proof inference. The cost counts exact scalar arithmetic and categorical draws; it does not assert bit complexity for arbitrary real inputs.
--
--   Differences from the source:
--
--   - reading: the ec14 proof infers the epsilon loss from the unrefined inverse-square sum → the theorem keeps the exact printed C and full guarantee, with the repaired first-failure estimate documented locally; reason: first failure is impossible at t=1 and the t=2 inventory law has at most two states, giving total failure probability below 6/(e*pi^2*C)
--   - encoding: runtime is polynomial in 1/epsilon,k,T,m in the sampling/arithmetic model → explicit bounded loops, least-index scans and a uniform polynomial operation bound; reason: one categorical sampling node is an oracle operation; numerical prices use scalar arithmetic, with initialization and final choice charged
--   - encoding: independent valuations are described as probability vectors → Mathlib PMF inputs and their explicit product masses; reason: every finite grid distribution is included and independence is constructed, not assumed from a conclusion
--   - encoding: prices r^(1),...,r^(m),infinity and valuation values → price codes 0,...,m, with m meaning rejection, and valuation indices 0,...,m; reason: this is a bijection on the strictly increasing positive price grid; rejection has zero revenue
--   - generalization: competitive horizons T are positive → the revenue and law statements also include T=0; reason: the empty execution and empty optimum both have revenue zero
--   - generalization: Theorem 5 asserts polynomial runtime for Algorithm 2 → the implemented selector is minimal, the exact ceiling is positive and bounded, and explicit uniform operation and transition bounds hold on every leaf, including leaves of weight zero; reason: these structural assertions and uniform bounds imply the full source runtime clause for the concrete least-index implementation without imposing an efficiency premise
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, p. 23, Theorem 5

import Mathlib
import Definitions.Def_ValTrackRM_Public_Supplement_Sampling

namespace ValTrackRM.Public.Supplement

theorem theorem_5
    (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ)
    (hr0 : r 0 = 0) (hr : ∀ j < m, r j < r (j + 1))
    (ν : ℕ → PMF (Fin (m + 1))) (T : ℕ) (ε : ℝ) (hε : 0 < ε) :
    let C := sampleConstant ε
    let sel := leastSelector (show 0 < k from hk)
    isMin sel ∧ 1 ≤ C ∧
    ((C : ℝ) ≤ 1 + 6 / (Real.exp 1 * Real.pi ^ 2 * ε)) ∧
    ((1 / qSum r m - ε) * expectedOpt r k ν T ≤ samplingRevenue r sel ν C T false) ∧
    (∀ x ∈ publicRun r sel ν C false T,
      x.1.simulatedTransitions ≤ C * (k + 1) * T ^ 4 ∧
      (x.1.operations : ℝ) ≤
        1000 * (2 + 6 / (Real.exp 1 * Real.pi ^ 2 * ε)) *
          (k + 1 : ℝ) ^ 2 * (m + 1 : ℝ) ^ 3 * (T + 1 : ℝ) ^ 4) := by sorry

end ValTrackRM.Public.Supplement
