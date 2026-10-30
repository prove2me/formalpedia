-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_finite_prior
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.finite_prior
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:17:21.869916+00:00
-- url     : https://prove2.me/theorems/5309e272-f251-4760-a825-664219ecdeae
-- title:
--   §III.C Eqs.(79)–(80): finite Gaussian-prior coherent-state cloning
-- statement:
--   For $\Sigma>0$, take the normalized prior $P(\alpha)=e^{-|\alpha|^2/(2\Sigma^2)}/(2\pi\Sigma^2)$. An actual amplifier and balanced splitter, with vacuum auxiliary modes, achieves the common prior-averaged single-clone fidelity
--
--   $$
--   \overline F=\begin{cases}(4\Sigma^2+2)/(6\Sigma^2+1),&\Sigma^2\ge\tfrac12+1/\sqrt2,\\[2pt]1/[1+(3-2\sqrt2)\Sigma^2],&\Sigma^2<\tfrac12+1/\sqrt2.\end{cases}
--   $$
--
--   The broad-prior gain is 8Σ⁴/(2Σ²+1)²; the narrow-prior gain is corrected to one. The theorem includes actual reduced densities and integrability and asserts achievability, not global optimality or pointwise universality.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 19, §III.C Eqs.(79)–(80): finite Gaussian-prior coherent-state cloning

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P40

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open MeasureTheory Filter

open scoped Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P12 (sigma)

open QAlgorithms.Papers.Independent.Dependency50.P48 (pureFidelity)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P16
  (CloneMap IsBoseInputChannel coherentTensor tensorWithIdentity canonicalCloner
   HasBoseOutput HasBlackCowCoefficient canonicalCoefficient oneMixed)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector siteObservable)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeHilbert ModeOperator IsModeDensity FockWeylSystem)

open QAlgorithms.Papers.Independent.Renew46.P41
  (coherentProduct NormalizedCoherent IsReducedDensity FockCanonicalAction
   ModeUnitary twoModeAmplifierQuadratures modeMixingQuadratures embeddedOpticalBeam
   displacedThermal cloneNoise cloneFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentProjector)

/-- III.C, PDF p.19 Eqs.(79)–(80): achievable PRIOR-AVERAGED fidelity, not a
claim of global optimality. The gain below the printed threshold is corrected to one. -/
theorem finite_prior (Sigma : ℝ) (hSigma : 0 < Sigma)
    (W : FockWeylSystem 3) (Wone : FockWeylSystem 1) :
    1 ≤ priorGain Sigma ∧ Integrable (priorWeight Sigma) volume ∧
    (∫ alpha : ℂ, priorWeight Sigma alpha) = 1 ∧
    ∃ A B : ModeUnitary 3,
      FockCanonicalAction W A (twoModeAmplifierQuadratures (0 : Fin 3) 2 (priorGain Sigma)) ∧
      FockCanonicalAction W B (modeMixingQuadratures (embeddedOpticalBeam (0 : Fin 3) 1 (Real.pi / 4))) ∧
      (∀ alpha : ℂ,
        NormalizedCoherent (fun k : Fin 3 => if k = 0 then alpha else 0) ∧
        IsModeDensity (priorClone Wone Sigma alpha) ∧
        ∀ k : Fin 2, IsReducedDensity
          (InnerProductSpace.rankOne ℂ
            ((A.trans B) (coherentProduct (fun k : Fin 3 => if k = 0 then alpha else 0)))
            ((A.trans B) (coherentProduct (fun k : Fin 3 => if k = 0 then alpha else 0))))
          ⟨k.val, by omega⟩ (priorClone Wone Sigma alpha)) ∧
      Integrable (priorIntegrand Wone Sigma) volume ∧
      (∫ alpha : ℂ, priorIntegrand Wone Sigma alpha) = priorFidelity Sigma := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
