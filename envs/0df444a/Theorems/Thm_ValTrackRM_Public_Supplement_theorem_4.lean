-- Prove2me | Theorems.Thm_ValTrackRM_Public_Supplement_theorem_4
-- name    : ValTrackRM.Public.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:01:54.168008+00:00
-- url     : https://prove2.me/theorems/0806cae0-547e-4cfb-82f6-2158835d0af9
-- title:
--   Theorem 4 — joint exact expected revenue (corrected: source typo)
-- statement:
--   For any independent grid-valuation laws $\nu_1,\ldots,\nu_T$, positive starting inventory and nonempty strictly increasing positive price grid, Exp and Algorithm 1 have identical joint expected revenues. For every fixed valuation realization $u=(u_1,\ldots,u_T)$, Algorithm 1 also has the exact internal expectation $\mathbb E_{\rm internal}[\mathrm{ALG}^{A1}(u)]=\mathrm{OPT}(u)/q$. Consequently,
--   $$
--   \mathbb E[\mathrm{ALG}^{\mathrm{Exp}}]=\mathbb E[\mathrm{ALG}^{A1}]=\frac{\mathbb E[\mathrm{OPT}]}{q},
--   \qquad \mathbb E[\mathrm{ALG}^{\mathrm{Exp}}]\ge c^*(\mathcal P)\mathbb E[\mathrm{OPT}].
--   $$
--   All four assertions appear in the Lean conjunction. This is the full stochastic competitiveness conclusion, including distributions with zero expected demand.
--
--   **Formalization Note** The printed middle sentence omits the internal expectation. The ec5 closing equality, ec13 revenue calculation, ec15 equality and p.20 warning support the expectation convention used here.
--
--   Differences from the source:
--
--   - correction: the middle sentence of Theorem 4 states ALG^A1=OPT/q without expectation → for every fixed realization the internal expected revenue equals OPT/q; reason: ec5, ec13, ec15 and p.20 distinguish pathwise revenue from internal expectation
--   - generalization: Algorithm 1 leaves arg-min ties unspecified → every fixed minimum-level selector is allowed; reason: the assignment must be deterministic for a fixed valuation prefix; no special tie-break is used
--   - encoding: independent valuations are described as probability vectors → Mathlib PMF inputs and their explicit product masses; reason: every finite grid distribution is included and independence is constructed, not assumed from a conclusion
--   - encoding: prices r^(1),...,r^(m),infinity and valuation values → price codes 0,...,m, with m meaning rejection, and valuation indices 0,...,m; reason: this is a bijection on the strictly increasing positive price grid; rejection has zero revenue
--   - generalization: competitive horizons T are positive → the revenue and law statements also include T=0; reason: the empty execution and empty optimum both have revenue zero
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, p. 19, Theorem 4

import Mathlib
import Definitions.Def_ValTrackRM_Public_Supplement_Stochastic

namespace ValTrackRM.Public.Supplement

theorem theorem_4
    (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ)
    (hr0 : r 0 = 0) (hr : ∀ j < m, r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : isMin sel)
    (ν : ℕ → PMF (Fin (m + 1))) (T : ℕ) :
    stochasticRevenue r k (expKernel r sel ν) ν T = jointA1Revenue r sel ν T ∧
    (∀ V : Fin T → Fin (m + 1),
      expRevenue r sel (List.ofFn V) = opt r k (List.ofFn V) / qSum r m) ∧
    stochasticRevenue r k (expKernel r sel ν) ν T = expectedOpt r k ν T / qSum r m ∧
    cStar r m * expectedOpt r k ν T ≤ stochasticRevenue r k (expKernel r sel ν) ν T := by sorry

end ValTrackRM.Public.Supplement
