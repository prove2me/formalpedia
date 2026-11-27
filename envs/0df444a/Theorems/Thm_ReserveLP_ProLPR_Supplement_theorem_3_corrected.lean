-- Prove2me | Theorems.Thm_ReserveLP_ProLPR_Supplement_theorem_3_corrected
-- name    : ReserveLP.ProLPR.Supplement.theorem_3_corrected
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T23:08:30.919718+00:00
-- url     : https://prove2.me/theorems/24a5701f-c0ba-4efd-9f58-30aff1e0282c
-- title:
--   Theorem 3 (corrected: exact constant and limit quantifiers) — weighted tightness of the analysis
-- statement:
--   Write $c^\star=2(\sqrt2-1)e^{\sqrt2-2}$ and $\alpha=(1+c^\star)^{-1}$. For every real $\eta>0$ there exist finite nonnegative bid data $D$, strictly positive real auction weights $w_a$, and an optimal pair $(s,q)$ for the weighted Profile-LP objective $L_D(w,s)>0$ such that
--
--   $$\max\!\left(\mathbb E\!\left[\sum_a w_a\mathrm{Rev}_a(r^{\mathcal R})\right],\sum_a w_a\mathrm{Rev}_a(0)\right)\le(\alpha+\eta)L_D(w,s).$$
--
--   The same witnesses satisfy weighted optimality and the displayed bound. The theorem concerns tightness of the analysis that compares expected rounded revenue with deterministic zero-reserve revenue. It does not assert tightness of the expected revenue of the better choice made separately in each realization.
--
--   **Formalization Note.** This explicitly corrects the printed Theorem 3, rather than claiming its literal $0.684$ inequality. Its proof's finite formulas have limiting ratio $\alpha\approx0.684388312530>0.684$ and use both positive perturbations tending to zero and unbounded finite buyer counts. The finite formulas and the obstruction to the printed coefficient are retained in DISPROOF.md and the source audit. The proof's final $\theta=\sqrt2$ is read as $\theta=\sqrt2-1$, and the marginal for the two special buyers is $q_{i,1+\epsilon}=1-q_{i,0}$; these proof corrections do not add premises to this target.
--
--   Differences from the source:
--   - correction: one finite weighted instance with max(E[weighted rounded revenue],weighted zero revenue) ≤ 0.684 times its optimal weighted LP value → for every η>0, a finite positive weighted instance and an optimal pair with the same maximum ≤ ((1+cStar)⁻¹+η) times its positive weighted LP value; reason: the exact finite formulas on pages 18–19 converge to α=(1+cStar)⁻¹≈0.684388312530, strictly above 0.684, and require ε→0 and k→∞; this is an explicit corrected_result, not an equivalent version of the printed existential claim
--   - reading: positive real weights and an optimal LP solution in the weighted problem → strictly positive real weights, weighted LP optimality and positive weighted LP objective for the same witnesses; reason: page 18 changes the objective only; the source construction attains a positive per-auction upper bound
--   - encoding: arbitrary finite sets, product rounding and an outside maximum → existential Fin m, Fin n and finite product-law sums followed by max; reason: there is no bound on cardinalities, integer restriction on weights, or change to E[max]; the published auction conventions are inherited
-- source:
--   Derakhshan, Golrezaei, Paes Leme, LP-based Approximation for Personalized Reserve Prices, arXiv:1905.01526v5, pp. 18–19, Theorem 3 (corrected limit statement)

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Supplement_WeightedModel

namespace ReserveLP.ProLPR.Supplement

/-- Corrected limit formulation supported by the finite construction on pp. 18–19.
This changes both the printed coefficient and the finite-attainment quantifiers. -/
theorem theorem_3_corrected (η : ℝ) (hη : 0 < η) :
    ∃ (m n : ℕ) (D : DataSet (Fin m) (Fin n)) (w : Fin m → ℝ)
      (s : Fin m → Profile (Fin n) → ℝ) (q : Fin n → ℝ → ℝ),
      (∀ a, 0 < w a) ∧ weightedLPOptimal D w s q ∧
      0 < weightedLPObj D w s ∧
      max (weightedRound D w q) (zeroRev D w) ≤
        ((1 + cStar)⁻¹ + η) * weightedLPObj D w s := by sorry

end ReserveLP.ProLPR.Supplement
