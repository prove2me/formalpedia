-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P100_relativeDistance_finite_and_attained
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P100.relativeDistance_finite_and_attained
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:27:00.856191+00:00
-- url     : https://prove2.me/theorems/43282272-44a8-4e24-af42-26966d1596b0
-- title:
--   Existence and finiteness of a closest feasible state
-- statement:
--   Let $H$ have arbitrary positive finite dimension $N$, and let $D$ be a compact real-convex set of density matrices containing $I/N$. Use natural logarithms and define the extended infimum $E_D(\sigma)=\inf_{\rho\in D}S(\sigma\Vert\rho)$, with infinite relative entropy at a support violation. Then every density matrix $\sigma$ has finite distance and an attaining feasible state:
--
--   $$
--   E_D(\sigma)<\infty,
--   \qquad
--   \exists\,\widehat\rho\in D:\quad S(\sigma\Vert\widehat\rho)=E_D(\sigma).
--   $$
--
--   This makes the notion of a closest feasible state well-defined as a nonempty set of optimizers. It does not assert uniqueness or positive definiteness of an optimizer.
--
--   **Formalization Note** The accepted infimum and its attaining comparisons are stored in bits. Multiplication by the positive constant $\log 2$ gives the natural-logarithm values and preserves finiteness and every minimizing equality.
-- source:
--   Continuity of Relative Entropy of Entanglement, arXiv:quant-ph/9910002v1, PDF p. 2, Proof: construction of rho-hat

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

/-- Proof, PDF p.2: every state has a finite distance attained by a state
in D. All assumptions on D from the theorem are carried forward. Minimizers
may be singular and are not required to be unique. -/
theorem relativeDistance_finite_and_attained
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (D : Set (Matrix I I ℂ))
    (hstates : ∀ rho ∈ D, IsDensityMatrix rho)
    (hcompact : IsCompact D) (hconvex : Convex ℝ D)
    (hmixed : (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ) ∈ D)
    (sigma : Matrix I I ℂ) (hsigma : IsDensityMatrix sigma) :
    0 ≤ relativeDistance D sigma ∧ relativeDistance D sigma < ⊤ ∧
      ∃ rhoHat ∈ D,
        positiveOperatorRelativeEntropyBits sigma rhoHat = relativeDistance D sigma := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P100

end
