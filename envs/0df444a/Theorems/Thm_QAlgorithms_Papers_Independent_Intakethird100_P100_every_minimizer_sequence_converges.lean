-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P100_every_minimizer_sequence_converges
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P100.every_minimizer_sequence_converges
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:28:24.146524+00:00
-- url     : https://prove2.me/theorems/c11a9703-4703-4bfb-adc2-da7d4785140e
-- title:
--   Every minimizing sequence converges to the free limit
-- statement:
--   Let $H$ have positive finite dimension $N$, and let $D$ be a compact real-convex set of density matrices containing $I/N$. Put $E_D(\omega)=\inf_{\rho\in D}S(\omega\Vert\rho)$, using support-aware relative entropy and natural logarithms. Suppose density matrices $\sigma_n$ converge in full trace norm to a state $\sigma\in D$. For every selection of attaining states $\widehat\rho_n\in D$ satisfying $S(\sigma_n\Vert\widehat\rho_n)=E_D(\sigma_n)$, one has
--
--   $$
--   \|\sigma_n-\sigma\|_1\longrightarrow0
--   \quad\Longrightarrow\quad
--   \|\widehat\rho_n-\sigma\|_1\longrightarrow0.
--   $$
--
--   The conclusion holds for every sequence of minimizers, even when minimizers away from the free limit are nonunique.
--
--   **Formalization Note** The accepted infimum and its attaining comparisons are stored in bits. Multiplication by the positive constant $\log 2$ gives the natural-logarithm values and preserves finiteness and every minimizing equality.
-- source:
--   Continuity of Relative Entropy of Entanglement, arXiv:quant-ph/9910002v1, PDF p. 3, Corollary

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P100

noncomputable section

open Filter

open scoped ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P100

open QAlgorithms.Papers.Independent.Dependency50.P15
  (relativeDistance relativeDistanceValue positiveOperatorRelativeEntropyBits groupedTensorPower)

open QAlgorithms.Papers.Independent.Information100.P54
  (relativeEntropyBits relativeEntanglement)

/-- Corollary, PDF p.3: every selection of attaining states converges to
the free limit. There is no uniqueness hypothesis and no uniform-in-n
small-distance premise; convergence eventually supplies the local threshold. -/
theorem every_minimizer_sequence_converges
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (D : Set (Matrix I I ℂ))
    (hstates : ∀ rho ∈ D, IsDensityMatrix rho)
    (hcompact : IsCompact D) (hconvex : Convex ℝ D)
    (hmixed : (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ) ∈ D)
    (sigma : Matrix I I ℂ) (hsigma : sigma ∈ D)
    (sigmaSeq rhoHat : ℕ → Matrix I I ℂ)
    (hseq : ∀ n, IsDensityMatrix (sigmaSeq n))
    (hconverges : Tendsto (fun n => traceNorm (sigmaSeq n - sigma)) atTop (nhds 0))
    (hminimizers : ∀ n, rhoHat n ∈ D ∧
      positiveOperatorRelativeEntropyBits (sigmaSeq n) (rhoHat n) = relativeDistance D (sigmaSeq n)) :
    Tendsto (fun n => traceNorm (rhoHat n - sigma)) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P100

end
