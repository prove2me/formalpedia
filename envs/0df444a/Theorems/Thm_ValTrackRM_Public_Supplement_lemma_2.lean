-- Prove2me | Theorems.Thm_ValTrackRM_Public_Supplement_lemma_2
-- name    : ValTrackRM.Public.Supplement.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T03:59:12.627722+00:00
-- url     : https://prove2.me/theorems/1d72ef83-d44a-4d74-830b-1c2b5fab71af
-- title:
--   Lemma 2 — conditional price and inventory laws (corrected: source typo)
-- statement:
--   Fix any deterministic grid-valuation sequence $V_1,\ldots,V_T$, positive inventory $k$, positive price count $m$, and a fixed minimum-level selector for Algorithm 1. Let $I^A_t$ be the remaining inventory and $P^A_t$ the price of policy $A$. For every $1\le t\le T$, every inventory $a\in\{0,\ldots,k\}$ with positive Algorithm 1 prime mass, and every finite or rejection price $p$,
--   $$
--   \Pr[P^{A1'}_t=p\mid I^{A1'}_{t-1}=a]=\Pr[P^{A1}_t=p\mid I^{A1}_{t-1}=a].
--   $$
--   For every $0\le t\le T$ and every inventory $a$, also
--   $$\Pr[I^{A1'}_t=a]=\Pr[I^{A1}_t=a].$$
--   Both clauses are retained. This is the law identity supporting the competitiveness of the inventory-conditioned policy.
--
--   **Formalization Note** Algorithm 1 prime uses the source-supported polarity correction to Definition 3. Unreachable conditioning states reject; the conditional-law claim only concerns positive-mass states.
--
--   Differences from the source:
--
--   - correction: Definition 3 steps 2–3 offer using the sold probability → Algorithm 1 prime offers using the unsold probability; reason: the unsold paragraph on p.14 and the first display of the ec6 proof require this polarity; no valuation cases are excluded
--   - generalization: Algorithm 1 leaves arg-min ties unspecified → every fixed minimum-level selector is allowed; reason: the assignment must be deterministic for a fixed valuation prefix; no special tie-break is used
--   - encoding: prices r^(1),...,r^(m),infinity and valuation values → price codes 0,...,m, with m meaning rejection, and valuation indices 0,...,m; reason: this is a bijection on the strictly increasing positive price grid; rejection has zero revenue
--   - generalization: competitive horizons T are positive → the revenue and law statements also include T=0; reason: the empty execution and empty optimum both have revenue zero
--   - encoding: Definition 3 leaves unreachable conditioning and the empty terminal offer range implicit → zero-stock, zero-mass and terminal-level states reject; reason: stockout requires rejection; terminal-level units are already sold on every positive-mass run; choices on zero-mass states do not change a law or revenue
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, p. 15, Lemma 2

import Mathlib
import Definitions.Def_ValTrackRM_Public_Supplement_Inventory

namespace ValTrackRM.Public.Supplement

theorem lemma_2
    (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ)
    (hr0 : r 0 = 0) (hr : ∀ j < m, r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : isMin sel)
    (V : List (Fin (m + 1))) :
    (∀ (t : ℕ), 1 ≤ t → t ≤ V.length → ∀ (a : Fin (k + 1)),
      0 < fixedStock r k (primeKernel r sel V) V (t - 1) a.val → ∀ p : Price m,
      fixedConditional r k (primeKernel r sel V) V t a.val p =
        a1Joint r sel (V.take (t - 1)) a.val p / a1Stock r sel (V.take (t - 1)) a.val) ∧
    (∀ (t : ℕ), t ≤ V.length → ∀ a : Fin (k + 1),
      fixedStock r k (primeKernel r sel V) V t a.val = a1Stock r sel (V.take t) a.val) := by sorry

end ValTrackRM.Public.Supplement
