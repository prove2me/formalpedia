-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_common_limit_convex_domination
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.common_limit_convex_domination
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:43:10.468374+00:00
-- url     : https://prove2.me/theorems/d8922490-ef5d-4bf0-bb46-3db6a5f69ed1
-- title:
--   Lemma 4.2: common positive-definite limit permits convex domination
-- statement:
--   Let $d\ge1$, and let $\rho_N^{(1)},\rho_N^{(2)}$ be density-state sequences on $\mathbb C^d$ that converge to the same positive-definite state $\rho$. For every $0<\lambda<1$, there are an integer $N_\lambda$ and a sequence of density states $\sigma_N$ such that
--   $$\rho_N^{(1)}=\lambda\rho_N^{(2)}+(1-\lambda)\sigma_N\qquad(N>N_\lambda).$$
--   Every $\sigma_N$, including early terms, is a density state. This domination statement has no estimation-scheme or LDP assumption.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 12, Lemma 4.2 / (39)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.12-13, Lemma 4.2, (39): all terms of the third sequence are states,
including the unconstrained early terms. No estimation or LDP premise is used. -/
theorem common_limit_convex_domination {d : ℕ} (hd : 0 < d)
    (rho : DensityOutcome d) (hpos : rho.val.PosDef) (a b : ℕ → DensityOutcome d)
    (ha : Tendsto a atTop (nhds rho)) (hb : Tendsto b atTop (nhds rho))
    (lambda : ℝ) (hlambda : 0 < lambda) (hlambdaOne : lambda < 1) :
    ∃ threshold : ℕ, ∃ sigma : ℕ → DensityOutcome d, ∀ k, threshold < k+1 →
      (a k).val = (lambda : ℂ) • (b k).val + ((1-lambda : ℝ) : ℂ) • (sigma k).val := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
