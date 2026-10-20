-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_asymptotic_F_attainment
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.asymptotic_F_attainment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:48:43.286166+00:00
-- url     : https://prove2.me/theorems/efd0db78-726b-4451-aa6f-d155d0961954
-- title:
--   Asymptotic pinching and maximum-measurement attainment of F
-- statement:
--   Let ρ,σ≥0 have nested supports and let α≥1. Put ρₙ=ρ^{⊗n}, σₙ=σ^{⊗n}, and let ρ̂ₙ be the pinching of ρₙ in the eigenspaces of σₙ. Maxima below are attained for each positive n, over all finite POVMs, with no fixed outcome cardinality. In the extended-real topology,
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   $$
--   F_\alpha(\rho\Vert\sigma)=\lim_{n\to\infty}\frac1n F_\alpha(\widehat\rho_n\Vert\sigma_n)=\lim_{n\to\infty}\frac1n\max_M F_\alpha^M(\rho_n\Vert\sigma_n).
--   $$
--
--   The two regularized attainability limits connect the quantum functional to commuting pinched and measured models.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 6, Theorem III.7 (asymptotic attainability)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.6: Asymptotic pinching and maximum-measurement attainment of F. Suprema are defined in EReal, and a separate quantified equality asserts actual maximum attainment. Sequences use n+1 copies, exactly reindexing positive n. -/
theorem asymptotic_F_attainment (rho sigma : Mat I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) (hsupp : SupportLE rho sigma) (alpha : ℝ) (ha : 1 ≤ alpha) :
    (∀ n : ℕ, 1 ≤ n → ∃ M : POVM (Fin n → I),
      measuredF alpha (copies n rho) (copies n sigma) M =
        maxMeasuredF alpha (copies n rho) (copies n sigma)) ∧
    Tendsto (fun n => scaled n (F alpha
      (pinch (copies (n + 1) sigma) (copies (n + 1) rho)) (copies (n + 1) sigma)))
      atTop (nhds (F alpha rho sigma)) ∧
    Tendsto (fun n => scaled n (maxMeasuredF alpha (copies (n + 1) rho) (copies (n + 1) sigma)))
      atTop (nhds (F alpha rho sigma)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
