-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P21_trace_concavity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P21.trace_concavity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:53:49.177746+00:00
-- url     : https://prove2.me/theorems/5685e2af-c89c-467b-9914-eb1bcce87d7b
-- title:
--   Scalar concavity implies concavity of spectral trace
-- statement:
--   Let $R,S$ be positive semidefinite trace-one matrices of the same positive finite dimension, let $p\in[0,1]$, and let $f:\mathbb R\to\mathbb R$ be concave on $[0,1]$. Write $f(R)$ for spectral functional calculus and $\operatorname{Tr}_{\mathbb R}$ for the real part of the trace. Then
--
--   $$
--   \operatorname{Tr}_{\mathbb R}f(pR+(1-p)S)\ge p\operatorname{Tr}_{\mathbb R}f(R)+(1-p)\operatorname{Tr}_{\mathbb R}f(S).
--   $$
--
--   In particular the marginal costs $L(R)=2(1-\operatorname{Tr}_{\mathbb R}R^2)$ and $\sqrt{L(R)}$ obey the same concavity inequality. The spectral trace and $L$ are invariant under unitary conjugation, and therefore so is $\sqrt L$. No operator-concavity hypothesis on $f$ is needed.
--
--   This is the finite spectral-trace fact used to obtain the concave marginal costs for concurrence and tangle.
-- source:
--   I-concurrence and tangle for isotropic states, arXiv:quant-ph/0208002v1, PDF p. 4, §2, (2.3): trace of a scalar concave spectral function is concave

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P21

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P03
  (PureEnsemble convexRoof pureConcurrence concurrence SchmidtData schmidtVector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.4--5, (2.3): scalar concavity on [0,1] implies spectral trace
concavity on density matrices; no operator-concavity hypothesis is added. -/
theorem trace_concavity (d : ℕ) (hd : 0 < d) (f : ℝ → ℝ)
    (hf : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (rho sigma : Matrix (Fin d) (Fin d) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    p * spectralTrace f rho + (1 - p) * spectralTrace f sigma ≤
      spectralTrace f ((p : ℂ) • rho + ((1 - p : ℝ) : ℂ) • sigma) ∧
    p * marginalTangle rho + (1-p) * marginalTangle sigma ≤
      marginalTangle ((p : ℂ) • rho + ((1-p : ℝ) : ℂ) • sigma) ∧
    p * Real.sqrt (marginalTangle rho) + (1-p) * Real.sqrt (marginalTangle sigma) ≤
      Real.sqrt (marginalTangle ((p : ℂ) • rho + ((1-p : ℝ) : ℂ) • sigma)) ∧
    (∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      spectralTrace f ((U : Matrix (Fin d) (Fin d) ℂ) * rho *
        (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) = spectralTrace f rho ∧
      marginalTangle ((U : Matrix (Fin d) (Fin d) ℂ) * rho *
        (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) = marginalTangle rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P21

end
