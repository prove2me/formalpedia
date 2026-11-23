-- Prove2me | Theorems.Thm_WeightedMajority_Shifting_Supplement_theorem_7_1
-- name    : WeightedMajority.Shifting.Supplement.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:56:41.729862+00:00
-- url     : https://prove2.me/theorems/0915ba9e-2ab2-4fd6-822b-1e7db5c5a185
-- title:
--   Theorem 7.1 — exact finite integer mistake budgets
-- statement:
--   Let $\phi_1,\ldots,\phi_n:X\to\{0,1\}$ be a finite pool, with nonnegative integer budgets $M_1,\ldots,M_n$ such that $\sum_i2^{-M_i}<2$. Run WM with $\beta=0$ and initial weights $2^{-M_i}$, allowing either prediction at every tie. For each member $i$ and every finite trial sequence whose labels equal $\phi_i$ at its instances,
--
--   $$M_{\rm WM}(\mathcal S)\le M_i.$$
--
--   The guarantee is individual to the consistent member, with no shattering assumption and no restriction on the instance domain or horizon. It uses exactly the published WM run and mistake count.
--
--   Differences from the source:
--   - encoding: indices 1 through n and weights 2 to the power minus M_i → Fin n and the positive weights 1 / 2^M_i; reason: natural exponents and reciprocals represent the same dyadic weights
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), DOI 10.1006/inco.1994.1009, p. 243, Theorem 7.1

import Definitions.Def_WeightedMajority_Basic_IsWMRun

namespace WeightedMajority.Shifting.Supplement

theorem theorem_7_1 {X : Type*} {n T : ℕ} (φ : Fin n → X → Bool) (M : Fin n → ℕ)
    (instances : Fin T → X) (label prediction : Fin T → Bool) (w : ℕ → Fin n → ℝ)
    (hsum : ∑ i : Fin n, (1 / (2 : ℝ) ^ M i) < 2)
    (hrun : WeightedMajority.Basic.IsWMRun 0 (fun i => 1 / (2 : ℝ) ^ M i)
      (fun t i => φ i (instances t)) label w prediction)
    (i : Fin n) (hconsistent : ∀ t, label t = φ i (instances t)) :
    WeightedMajority.Basic.mistakeCount prediction label ≤ M i := by sorry

end WeightedMajority.Shifting.Supplement
