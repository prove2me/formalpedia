-- Prove2me | Theorems.Thm_ValTrackRM_Public_Supplement_lemma_4
-- name    : ValTrackRM.Public.Supplement.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:01:07.413488+00:00
-- url     : https://prove2.me/theorems/ec9fac6e-b75d-447e-a7c8-83a8bc46d717
-- title:
--   Lemma 4 — joint conditional price and inventory laws
-- statement:
--   Let $V_t$ be independently drawn from arbitrary, possibly different grid distributions $\nu_t$. Let $I^A_t$ and $P^A_t$ denote inventory and price of policy $A$, with Algorithm 1 averaged over both its hidden past valuations and its internal randomness. For $1\le t\le T$, every reachable Exp inventory $a$, and every finite or rejection price $p$,
--   $$\Pr[P^{\mathrm{Exp}}_t=p\mid I^{\mathrm{Exp}}_{t-1}=a]=\Pr[P^{A1}_t=p\mid I^{A1}_{t-1}=a].$$
--   For all $0\le t\le T$ and $a\in\{0,\ldots,k\}$,
--   $$\Pr[I^{\mathrm{Exp}}_t=a]=\Pr[I^{A1}_t=a].$$
--   These are both equations (4) and (5). They concern the joint stochastic model, and do not assert agreement on any particular hidden valuation history. The identities support the expected-revenue guarantee for Exp.
--
--   Differences from the source:
--
--   - generalization: Algorithm 1 leaves arg-min ties unspecified → every fixed minimum-level selector is allowed; reason: the assignment must be deterministic for a fixed valuation prefix; no special tie-break is used
--   - encoding: independent valuations are described as probability vectors → Mathlib PMF inputs and their explicit product masses; reason: every finite grid distribution is included and independence is constructed, not assumed from a conclusion
--   - encoding: prices r^(1),...,r^(m),infinity and valuation values → price codes 0,...,m, with m meaning rejection, and valuation indices 0,...,m; reason: this is a bijection on the strictly increasing positive price grid; rejection has zero revenue
--   - generalization: competitive horizons T are positive → the revenue and law statements also include T=0; reason: the empty execution and empty optimum both have revenue zero
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, p. 19, Lemma 4

import Mathlib
import Definitions.Def_ValTrackRM_Public_Supplement_Stochastic

namespace ValTrackRM.Public.Supplement

theorem lemma_4
    (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ)
    (hr0 : r 0 = 0) (hr : ∀ j < m, r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : isMin sel)
    (ν : ℕ → PMF (Fin (m + 1))) (T : ℕ) :
    (∀ (t : ℕ), 1 ≤ t → t ≤ T → ∀ (a : Fin (k + 1)),
      0 < stochasticStock r k (expKernel r sel ν) ν (t - 1) a.val → ∀ p : Price m,
      stochasticConditional r k (expKernel r sel ν) ν t a.val p =
        jointA1Price r sel ν (t - 1) a.val p / jointA1Stock r sel ν (t - 1) a.val) ∧
    (∀ (t : ℕ), t ≤ T → ∀ a : Fin (k + 1),
      stochasticStock r k (expKernel r sel ν) ν t a.val = jointA1Stock r sel ν t a.val) := by sorry

end ValTrackRM.Public.Supplement
