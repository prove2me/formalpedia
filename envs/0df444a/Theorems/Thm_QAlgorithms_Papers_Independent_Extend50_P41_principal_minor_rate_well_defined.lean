-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_principal_minor_rate_well_defined
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.principal_minor_rate_well_defined
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:52:40.742345+00:00
-- url     : https://prove2.me/theorems/397738e7-66f5-4755-bf04-c43b5cdbf738
-- title:
--   Lemma 4.15: well-definedness and positivity of the principal-minor rate
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   There is a unique nonnegative extended function $\widehat I$ satisfying, for every ordered probability vector $x$, every unitary $U$, and every state $\rho$,
--   $$\widehat I(\rho,U\rho_xU^*)=\sum_jx_j\log x_j-\sum_j(x_j-x_{j+1})\log\operatorname{pm}_j(U^*\rho U),\qquad x_{d+1}=0.$$
--   Here $\rho_x=\operatorname{diag}x$ and $\operatorname{pm}_j$ is the leading principal determinant. Use $0\log0=0$ and zero weight times an infinite logarithm equal to zero. In addition,
--   $$\widehat I(\rho,\sigma)=0\ \Longrightarrow\ \sigma=\rho.$$
--   The uniqueness concerns the rate function, not a choice of eigenvectors. This makes the displayed all-state rate well defined, including repeated eigenvalues and singular inputs.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 25, Lemma 4.15 / (131)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.25-26, Lemma 4.15, (131): well-definedness, uniqueness and
nonnegativity (encoded by ENNReal), and zero only at the input state.
The formula identity rules out artificial truncation in fullRate. -/
theorem principal_minor_rate_well_defined {d : ℕ} (hd : 0 < d) :
    (∀ (rho sigma : DensityOutcome d) (x : OrderedSpectrum d) (U : Matrix.unitaryGroup (Fin d) ℂ),
      sigma.val = (U : Matrix (Fin d) (Fin d) ℂ) * diagonalStateMatrix x * star (U : Matrix (Fin d) (Fin d) ℂ) →
      (fullRate rho sigma : EReal) = minorFormula rho U x) ∧
    (∀ J : DensityOutcome d → DensityOutcome d → ℝ≥0∞,
      (∀ (rho sigma : DensityOutcome d) (x : OrderedSpectrum d) (U : Matrix.unitaryGroup (Fin d) ℂ),
        sigma.val = (U : Matrix (Fin d) (Fin d) ℂ) * diagonalStateMatrix x * star (U : Matrix (Fin d) (Fin d) ℂ) →
        (J rho sigma : EReal) = minorFormula rho U x) → J = fullRate) ∧
    ∀ rho sigma : DensityOutcome d, fullRate rho sigma = 0 → sigma = rho := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
