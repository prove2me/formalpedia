-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P44_process_fidelity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P44.process_fidelity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:07:29.555812+00:00
-- url     : https://prove2.me/theorems/bc9a8bfa-bdf5-42aa-86fd-476e14c81694
-- title:
--   Finite renormalized process score
-- statement:
--   For a normalized centered physical two-mode Gaussian resource $V=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$, let $K$ be the unity-gain teleportation kernel and define the renormalized process score by $\mathcal F=2\pi K(0,0)$. With $R=\operatorname{diag}(1,-1)$, put $E'=RAR^T+RC+C^TR^T+B$. Then $E'$ is positive definite, its determinant is strictly positive, the resource slice below is integrable, and
--
--   $$\mathcal F=2\pi\int_{\mathbb R^2}W_{AB}(x,p,-x,p)\,dx\,dp=\frac{2}{\sqrt{\det E'}}.$$
--
--   The score is a finite real number for each finite physical Gaussian covariance, but is not a probability and has no universal upper bound. Setting $D=0$ in the covariance objective is purely formal and does not describe an input state. This separates the finite process score from the divergent ideal-EPR overlap.
-- source:
--   Improving fidelity of continuous-variable teleportation via local operations, arXiv:quant-ph/0202102v3, PDF p. 3, §II, Eqs.(18)–(21)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P44

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Claimed50.P44

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance pureCovariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.3, Eqs.(18)-(21). The renormalized score is 2 pi K(0,0),
not the divergent overlap of two ideal EPR distributions. -/
theorem process_fidelity (A B C : QuadratureMatrix)
    (hresource : PhysicalResource (resourceCov A B C)) :
    let W := resourceWigner (resourceCov A B C) 0
    let E := noiseBase 0 A B C 1
    E.PosDef ∧ 0 < E.det ∧
    Integrable (fun z : ℝ × ℝ => W ![z.1, z.2] ![-z.1, z.2]) ∧
    processScore W = 2 * Real.pi * phaseIntegral (fun z => W z ![-z 0, z 1]) ∧
    processScore W = 2 / Real.sqrt E.det := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P44

end
