-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaA_8
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemmaA_8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:48:46.636685+00:00
-- url     : https://prove2.me/theorems/ec8c467a-604c-4dca-a70b-e8e90542398c
-- title:
--   Quantum Stein asymptotics for testing entropy
-- statement:
--   Let $\rho$ be a density operator, $\sigma\ge0$ on the same nonzero finite-dimensional system, and $0<\epsilon<1$. Then, in the extended real line,
--
--   $$\lim_{n\to\infty}\frac1n D_H^\epsilon(\rho^{\otimes n}\|\sigma^{\otimes n})=D(\rho\|\sigma).$$
--
--   Both entropies use base-two logarithms and the testing quantity has acceptance at least $\epsilon$ and objective normalized by $\epsilon$. In particular, support failure is not removed by a finite-relative-entropy assumption.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 21, Lemma A.8

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Lemma A.8, Eq.155 (PDF p.21). The limit is in EReal, including support failure. -/
theorem lemmaA_8 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Op I) (hrho : IsDensityMatrix rho) (hsigma : sigma.PosSemidef)
    (epsilon : ℝ) (he : 0 < epsilon) (hlt : epsilon < 1) :
    Tendsto (fun n => (((n+1 : ℕ) : ℝ)⁻¹ : EReal) *
      normalizedTestingEntropyBits epsilon (matrixPower rho (n+1)) (matrixPower sigma (n+1)))
      atTop (nhds (normalizedRelativeEntropyBits rho sigma)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
