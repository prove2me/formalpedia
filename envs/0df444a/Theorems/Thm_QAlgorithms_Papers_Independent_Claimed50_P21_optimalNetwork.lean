-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P21_optimalNetwork
-- name    : QAlgorithms.Papers.Independent.Claimed50.P21.optimalNetwork
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:08:27.284705+00:00
-- url     : https://prove2.me/theorems/fdd73c4a-a03a-43de-9b23-e176a6420313
-- title:
--   Explicit optimal first isometry and Bell feed-forward realization
-- statement:
--   Fix $d\ge2$, normalized Haar measure on $\mathrm{SU}(d)$, and parameters $x,y\in[0,1]$ satisfying $x^2+y^2+2xy/d=1$. Define the first stage and the outcome-labelled second-stage Kraus operator by
--
--   $$
--   V^{[1]}|\psi\rangle_0=\frac1{\sqrt d}\bigl(y|\psi\rangle_1|I_d\rangle\!\rangle_{1'0'}+x|I_d\rangle\!\rangle_{11'}|\psi\rangle_{0'}\bigr),\qquad K_V=\sqrt d\,V_{0'\to3}\langle\!\langle V|_{2,1'}.
--   $$
--
--   The first stage is an isometry. The second stage is a normalized continuous instrument: $\int dV\,K_V^\dagger K_V=I$, and its Bell POVM density $B_V=d|V\rangle\!\rangle\langle\!\langle V|$ integrates to the identity on wires $(2,1')$. These integrals are integrable. Its definition is independent of $x,y$.
--
--   The two known stages, with exactly one unknown use $U$ between them, realize the complete rank-one density of Eq.(30). This density is admissible, attains the minimum disturbance at its information value, and has $F=1-(d^2-2)x^2/d^2$ and $G=(2-y^2)/d^2$. For every $U,V\in\mathrm{SU}(d)$ its conditional Kraus matrix is
--
--   $$
--   K_V(U\otimes I)V^{[1]}=M_{U,V}:=yU+x\operatorname{Tr}(V^\dagger U)V.
--   $$
--
--   For every input operator $\rho$, the conditional output is $M_{U,V}\rho M_{U,V}^\dagger$. For every unit input vector $\psi$, the outcome density equals $\|M_{U,V}\psi\|^2$, is integrable over $V$, and integrates to one.
--
--   This gives the explicit Bell measurement and feed-forward realization at every frontier point, including both endpoints. The conditional vector is subnormalized relative to the outcome law; its pointwise squared norm need not be at most one.
-- source:
--   Information - Disturbance Tradeoff in the Estimation of a Unitary Transformation, arXiv:1006.5665v2, PDF p. 8, §IV D, Eq.(40); Fig.4 on PDF p.9

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P21

noncomputable section

open MeasureTheory

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P21

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

/-- PDF pp.7–9, Eq.(40), Fig.4: explicit first isometry and Bell feed-forward,
including endpoint parameters, the whole Choi instrument, and outcome norm-square density.
The printed final-evolution trace on p.8 is corrected to Tr[V dagger U] using Eq.(40).
The instrument after the unknown use has input (2,1',0'), correcting the printed A2 to A1. -/
theorem optimalNetwork (d : ℕ) (hd : 2 ≤ d) (H : HaarLaw d)
    (x y : ℝ) (hxy : NormalizedParameters d x y) :
    (firstIsometry d x y)ᴴ * firstIsometry d x y = 1 ∧
    Integrable (fun V : SU d => (bellKraus V)ᴴ * bellKraus V) H.law ∧
    (∫ V : SU d, (bellKraus V)ᴴ * bellKraus V ∂H.law) = 1 ∧
    Integrable (fun V : SU d => bellEffect V) H.law ∧
    (∫ V : SU d, bellEffect V ∂H.law) = 1 ∧
    realizedDensity x y = optimalDensity (d := d) x y ∧
    IsHaarCombInstrument H (by omega) (realizedDensity x y) ∧
    channelScore H (realizedDensity x y) = 1 - ((d : ℝ)^2-2)*x^2/(d : ℝ)^2 ∧
    gain H (realizedDensity x y) = (2-y^2)/(d : ℝ)^2 ∧
    IsLeast (attainableDisturbances H (by omega) (normalizedInformation H (realizedDensity x y)))
      (disturbance H (realizedDensity x y)) ∧
    (∀ U V : SU d, bellKraus V * unknownUse U * firstIsometry d x y = conditionalMatrix x y U V) ∧
    (∀ (U V : SU d) (rho : Matrix (Wire d) (Wire d) ℂ),
      insertedOutput (realizedDensity x y V) U rho =
        conditionalMatrix x y U V * rho * (conditionalMatrix x y U V)ᴴ) ∧
    (∀ (U : SU d) (psi : EuclideanSpace ℂ (Wire d)), IsState psi →
      (∀ V : SU d, outcomeDensity (realizedDensity x y V) U (pureDensity psi) =
        ‖act (conditionalMatrix x y U V) psi‖^2) ∧
      Integrable (fun V : SU d => ‖act (conditionalMatrix x y U V) psi‖^2) H.law ∧
      (∫ V : SU d, ‖act (conditionalMatrix x y U V) psi‖^2 ∂H.law) = 1) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P21

end
