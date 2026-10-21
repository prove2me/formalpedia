-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P44_example_optimum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P44.example_optimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:11:56.377382+00:00
-- url     : https://prove2.me/theorems/fbabe0b9-7386-4287-b6bb-d1a946de80ff
-- title:
--   Exact coherent-input optimizer against every Bob Gaussian map
-- statement:
--   Take $r\ge0$, $a=\cosh(2r)$, $b=a+1/2$, $c=\sinh(2r)$ and the physical resource $A=aI$, $B=bI$, $C=\operatorname{diag}(-c,c)$. Set $r_{\rm th}=-\tfrac12\log(1/2)$ and
--
--   $$t=\begin{cases}c/(b-1),&r\le r_{\rm th},\\1,&r>r_{\rm th}.\end{cases}\qquad n_*=\begin{cases}a+1-c^2/(b-1),&r\le r_{\rm th},\\1/2+2e^{-2r},&r>r_{\rm th}.\end{cases}$$
--
--   The Bob channel $S=tI$, $G=(1-t^2)I$, with zero displacement, is completely positive and maximizes the outcome-averaged fidelity of every coherent input against all real Bob gains, CP noises, and affine displacements. Its fidelity is
--
--   $$F_{\rm CP}=\frac{2}{2+n_*}.$$
--
--   Among every Bob symplectic unitary and displacement, the identity is optimal with $F_{\rm symp}=2/(5/2+2e^{-2r})$. At $r=0$, $t=0$ and $F_{\rm CP}=1/2$; at the threshold $t=1$ and both branches agree. This specifies the exact channel, rather than only algebraic candidate roots.
-- source:
--   Improving fidelity of continuous-variable teleportation via local operations, arXiv:quant-ph/0202102v3, PDF p. 6, §IV, Eqs.(60)–(61), Fig.1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P44

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Claimed50.P44

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance pureCovariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF pp.6-7, Eqs.(60)-(61), Fig.1, b0=1/2: exact coherent-input
maximizer against ALL real Bob gains/noises and affine displacements. No
unproved general diagonal-optimality hypothesis is assumed. -/
theorem example_optimum (r : ℝ) (hr : 0 ≤ r) :
    let t := dampingGain r
    let W := exampleOutput r (t • (1 : QuadratureMatrix)) (dampingNoise r) 0
    PhysicalResource (exampleResource r) ∧ 0 ≤ t ∧ t ≤ 1 ∧
    GaussianCP (t • (1 : QuadratureMatrix)) (dampingNoise r) ∧
    0 < exampleOptimalNoise r ∧
    (∀ mean : PhasePoint, bellAverageFidelity 1 mean W = 2 / (2 + exampleOptimalNoise r)) ∧
    (∀ (S G : QuadratureMatrix) (d mean : PhasePoint), GaussianCP S G →
      bellAverageFidelity 1 mean (exampleOutput r S G d) ≤ bellAverageFidelity 1 mean W) ∧
    (∀ (S : QuadratureMatrix) (d mean : PhasePoint), Symplectic S →
      bellAverageFidelity 1 mean (exampleOutput r S 0 d) ≤
        bellAverageFidelity 1 mean (exampleOutput r 1 0 0)) ∧
    (∀ mean : PhasePoint, bellAverageFidelity 1 mean (exampleOutput r 1 0 0) =
      2 / (5 / 2 + 2 * Real.exp (-2 * r))) ∧
    (r = 0 → t = 0 ∧ ∀ mean : PhasePoint, bellAverageFidelity 1 mean W = 1 / 2) ∧
    (r = squeezingThreshold → t = 1 ∧
      exampleA r + 1 - exampleC r ^ 2 / (exampleB r - 1) =
        1 / 2 + 2 * Real.exp (-2 * r)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P44

end
