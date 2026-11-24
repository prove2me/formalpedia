-- Prove2me | Theorems.Thm_ValTrackRM_Public_Supplement_theorem_2
-- name    : ValTrackRM.Public.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:59:49.856088+00:00
-- url     : https://prove2.me/theorems/0ea3bc9f-87fc-4bbb-9789-151d65b2596d
-- title:
--   Theorem 2 — inventory-conditioned competitive guarantee (corrected: source typo)
-- statement:
--   Let $0=r^{(0)}<r^{(1)}<\cdots<r^{(m)}$ be a nonempty finite price grid, let $k\ge1$, and define $q=\sum_{j=1}^{m}(1-r^{(j-1)}/r^{(j)})$. For every deterministic grid-valuation sequence, corrected Algorithm 1 prime satisfies
--   $$\mathbb E[\mathrm{ALG}^{A1'}(V_1,\ldots,V_T)]\ge\frac{1}{q}\mathrm{OPT}(V_1,\ldots,V_T).$$
--   The expectation is the finite sum produced by its actual inventory recursion. The offline optimum is the published maximum total valuation of at most $k$ customers. This gives the full competitive guarantee for the policy conditioned only on remaining inventory and the revealed valuation prefix.
--
--   **Formalization Note** The unsold offer probability follows the p.14 paragraph and ec6 display correcting Definition 3.
--
--   Differences from the source:
--
--   - correction: Definition 3 steps 2–3 offer using the sold probability → Algorithm 1 prime offers using the unsold probability; reason: the unsold paragraph on p.14 and the first display of the ec6 proof require this polarity; no valuation cases are excluded
--   - generalization: Algorithm 1 leaves arg-min ties unspecified → every fixed minimum-level selector is allowed; reason: the assignment must be deterministic for a fixed valuation prefix; no special tie-break is used
--   - encoding: prices r^(1),...,r^(m),infinity and valuation values → price codes 0,...,m, with m meaning rejection, and valuation indices 0,...,m; reason: this is a bijection on the strictly increasing positive price grid; rejection has zero revenue
--   - generalization: competitive horizons T are positive → the revenue and law statements also include T=0; reason: the empty execution and empty optimum both have revenue zero
--   - encoding: Definition 3 leaves unreachable conditioning and the empty terminal offer range implicit → zero-stock, zero-mass and terminal-level states reject; reason: stockout requires rejection; terminal-level units are already sold on every positive-mass run; choices on zero-mass states do not change a law or revenue
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, p. 15, Theorem 2

import Mathlib
import Definitions.Def_ValTrackRM_Public_Supplement_Inventory

namespace ValTrackRM.Public.Supplement

theorem theorem_2
    (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ)
    (hr0 : r 0 = 0) (hr : ∀ j < m, r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : isMin sel)
    (V : List (Fin (m + 1))) :
    cStar r m * opt r k V ≤ fixedRevenue r k (primeKernel r sel V) V := by sorry

end ValTrackRM.Public.Supplement
