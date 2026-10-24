-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_theorem8
-- name    : QAlgorithms.Papers.Independent.Support50.P15.theorem8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:40:48.665414+00:00
-- url     : https://prove2.me/theorems/e84f5a40-1699-4b85-bda2-3d7499313ebc
-- title:
--   Maximum variance of the surprisal
-- statement:
--   For a normalized state $\rho$ in dimension $d$, let $V(\rho)=\sum_i p_i\log^2p_i-S(\rho)^2$ be the variance of its surprisal, where $p_i$ are its eigenvalues and zero eigenvalues contribute zero. Let $N(d)$ and $N_d$ be Eqs. (7)--(8). For $d\ge2$,
--
--   $$V(\rho)\le N(d)<N_d.$$
--
--   There is exactly one maximizing $r_d\in(0,1/2)$ in Eq. (7), and equality holds if and only if the eigenvalues, with multiplicities and in any order, are $1-r_d,r_d/(d-1),\ldots,r_d/(d-1)$. In dimension one $V(\rho)=0$. This gives the sharp dimension-only bound and its complete spectral equality characterization.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 8, theorem8

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Theorem 8, PDF p.8; proof pp.24--25. Eigenvalues are matched by a permutation, never by
an imposed order. The one-dimensional case is retained. -/
theorem theorem8 :
    (∀ a : EntropyState 1, surprisalVariance a.val = 0) ∧
    (∀ d : ℕ, 2 ≤ d →
      (∃! r : ℝ, r ∈ Set.Ioo 0 (1 / 2) ∧ varianceObjective d r = maxVariance d) ∧
      optimalMass d ∈ Set.Ioo 0 (1 / 2) ∧ varianceObjective d (optimalMass d) = maxVariance d ∧
      (∀ a : EntropyState d, surprisalVariance a.val ≤ maxVariance d ∧ maxVariance d < easyVariance d ∧
        (surprisalVariance a.val = maxVariance d ↔ ∃ e : Equiv.Perm (Fin d),
          ∀ i, ascEigenvalues a.val i = familyProb d (optimalMass d)
            (e (Fin.cast (Fintype.card_fin d) i))))) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
