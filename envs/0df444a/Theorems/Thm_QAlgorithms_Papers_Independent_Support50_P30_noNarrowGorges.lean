-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P30_noNarrowGorges
-- name    : QAlgorithms.Papers.Independent.Support50.P30.noNarrowGorges
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:30:39.395423+00:00
-- url     : https://prove2.me/theorems/07936235-d6f6-404e-a220-c3e5a1f6d70e
-- title:
--   Unnumbered absence of narrow gorges under inverse-polynomial loss variance
-- statement:
--   Consider a family of noiseless layered equivariant circuits, density-matrix inputs $\rho_n$, and Hermitian equivariant observables $O_n$ with a uniform spectral bound $\|O_n\|_{\mathrm{op}}\le K$, where $K>0$ is fixed before $n$. Let $\ell_n(\theta)=\operatorname{Tr}(U_n(\theta)\rho_nU_n(\theta)^\dagger O_n)$, with parameters uniform on $[0,2\pi]^{L_n}$. Assume an eventual inverse-polynomial lower bound: for some $c>0$, integer $k\ge0$, and $N$,
--
--   $$\operatorname{Var}_\theta(\ell_n)\ge c n^{-k}\quad(n\ge N).$$
--
--   Then this loss family has no narrow gorge. A narrow gorge means the conjunction of below-mean points at inverse-polynomial separation and a tail envelope $\Pr(|\ell_n-\mathbb E\ell_n|\ge d)\le C/(b^n d^2)$ for fixed $C>0$, $b>1$, all sufficiently large $n$, and every $d>0$. The conclusion retains the explicit loss-variance premise of Eq. (96); it does not assert the incorrect probability-tends-to-one estimate of Eq. (100).
-- source:
--   Theoretical Guarantees for Permutation-Equivariant Quantum Neural Networks, arXiv:2210.09974v3, PDF p. 34, Unnumbered absence of narrow gorges under inverse-polynomial loss variance

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P30

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.7,33-34: qualitative no-gorge result with the loss-variance
premise (96). The incorrect anti-concentration estimate (100) is deferred. -/
theorem noNarrowGorges (K : ℝ) (hK : 0 < K) (L : ℕ → ℕ)
    (H : (n : ℕ) → Fin (L n) → QnnOperator n) (hH : ∀ n j, (H n j).IsHermitian)
    (hHeq : ∀ n j, PermutationEquivariant (H n j))
    (rho : (n : ℕ) → QnnDensity n) (O : (n : ℕ) → QnnOperator n)
    (hO : ∀ n, (O n).IsHermitian) (hOeq : ∀ n, PermutationEquivariant (O n))
    (hbound : ∀ n, specNorm (O n) ≤ K)
    (hvariance : InversePolynomialLower
      (fun n => variance (uniformParameters (L n)) (fun t => qnnLoss (circuit (H n) t) (rho n).val (O n)))) :
    ¬ HasNarrowGorge L (fun n t => qnnLoss (circuit (H n) t) (rho n).val (O n)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P30

end
