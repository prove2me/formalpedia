-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_example_2_11
-- name    : QAlgorithms.Papers.Independent.Support50.P12.example_2_11
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:17:06.566308+00:00
-- url     : https://prove2.me/theorems/ac22178a-3289-4749-afcf-4a1e9ba890de
-- title:
--   Example 2.11
-- statement:
--   Let $A,B$ be positive semidefinite operators on a nonzero finite-dimensional complex Hilbert space. Let $f:[0,\infty)\to\mathbb R$ be continuous on $(0,\infty)$ with signed extended recession slope $\omega(f)=\lim_{x\to\infty}f(x)/x$. Write $S_f$ for the paper's quantum divergence, $Q_f(A,B)=\langle B^{1/2},f(L_AR_{B^{-1}})B^{1/2}\rangle_{\rm HS}$, and $X^0$ for the support projection. All powers vanish on the kernel, including exponent zero. Traces are representation traces.
--
--   The root fidelity $F(\rho,\sigma)=\operatorname{Tr}\sqrt{\rho^{1/2}\sigma\rho^{1/2}}$ has no representation by one admissible generator on quantum states of all finite dimensions:
--
--   $$
--   exists f\quad\forall\rho,\sigma\text{ density operators},\quad S_f(\rho\Vert\sigma)=F(\rho,\sigma).$$
--
--   The radical defines root fidelity, not its square. This separates fidelity from quantum $f$-divergences.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 8, Example 2.11

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- Example 2.11, PDF p.8: ROOT fidelity has no f-divergence representation on
quantum states of all dimensions. The radical was visually checked on the PDF. -/
theorem example_2_11 :
    ¬ ∃ f : ℝ → ℝ, DivergenceGenerator f ∧
      ∀ (n : ℕ), 0 < n → ∀ rho sigma : Mat (Fin n),
        AlgebraDensity ⊤ rho → AlgebraDensity ⊤ sigma →
        div f rho sigma = (tr (supportPower
          (supportPower rho (1 / 2) * sigma * supportPower rho (1 / 2)) (1 / 2)) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
