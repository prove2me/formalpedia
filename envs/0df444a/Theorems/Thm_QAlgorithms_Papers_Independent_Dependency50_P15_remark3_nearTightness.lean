-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P15_remark3_nearTightness
-- name    : QAlgorithms.Papers.Independent.Dependency50.P15.remark3_nearTightness
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:22:53.165983+00:00
-- url     : https://prove2.me/theorems/5b419e6e-33a2-4ab6-84dc-5b0dc2df918f
-- title:
--   Remark 3: explicit near-tightness example for Lemma 2
-- statement:
--   Let $d\ge2$, $0\le\varepsilon\le1$, and $\Phi_d=|\phi_d\rangle\langle\phi_d|$, where $|\phi_d\rangle=d^{-1/2}\sum_{j=0}^{d-1}|jj\rangle$ on $\mathbb C^d\otimes\mathbb C^d$. Define $\sigma=\Phi_d$ and $\rho=(1-\varepsilon)\Phi_d+\frac{\varepsilon}{d^2-1}(I-\Phi_d)$. Both are density states, and, writing $T$ for half the trace norm and $h_2$ for binary entropy in bits,
--
--   $$T(\rho,\sigma)=\varepsilon,\qquad S(A|B)_\rho-S(A|B)_\sigma=\varepsilon\log_2(d^2-1)+h_2(\varepsilon).$$
--
--   The difference equals $2\varepsilon\log_2d+h_2(\varepsilon)+O(\varepsilon/d^2)$: there are absolute $C>0$ and $N\ge2$ such that the absolute remainder is at most $C\varepsilon/d^2$ for every $d\ge N$ and every $\varepsilon\in[0,1]$. This constructed family demonstrates the near-tightness of Lemma 2.
-- source:
--   Tight uniform continuity bounds for quantum entropies: conditional entropy, relative entropy distance and energy constraints, arXiv:1507.07775v6, PDF p. 3, Remark 3: explicit near-tightness example for Lemma 2

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P15

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P15

open QAlgorithms.Papers.Independent.Information100.P08 (bellVector)

/-- Remark 3, PDF p.3: the exact displayed near-tightness family and its uniform
O(epsilon/d²) remainder. The coefficient epsilon/(d²−1) is confirmed in the PDF. -/
theorem remark3_nearTightness :
    (∀ (d : ℕ), 2 ≤ d → ∀ (epsilon : ℝ), 0 ≤ epsilon → epsilon ≤ 1 →
      let sigma := (pureDensity (bellVector d))
      let rho := isotropicDensity d epsilon
      IsDensityMatrix sigma ∧ IsDensityMatrix rho ∧ traceDistance rho sigma = epsilon ∧
      finiteConditionalEntropy rho - finiteConditionalEntropy sigma =
        epsilon * Real.logb 2 ((d : ℝ)^2 - 1) + binEntropy2 epsilon) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ d : ℕ, N ≤ d →
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ 1 →
      |(finiteConditionalEntropy (isotropicDensity d epsilon) -
          finiteConditionalEntropy (pureDensity (bellVector d))) -
        (2 * epsilon * Real.logb 2 (d : ℝ) + binEntropy2 epsilon)| ≤
          C * epsilon / (d : ℝ)^2) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P15

end
