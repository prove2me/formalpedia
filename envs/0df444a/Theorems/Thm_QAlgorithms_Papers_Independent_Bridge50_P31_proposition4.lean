-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_proposition4
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.proposition4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:55:08.869674+00:00
-- url     : https://prove2.me/theorems/3bba46bf-a134-40d7-be9a-01dee46660b4
-- title:
--   Proposition 4
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   For a positive symmetric operator-monotone function $f:(0,\infty)\to(0,\infty)$, put $\Delta_\rho=L_\rho R_\rho^{-1}$, $J_\rho^f=f(\Delta_\rho)R_\rho$, $\lambda_\rho^f(x,y)=\operatorname{Tr}((J_\rho^f)^{-1}(x)y)$ and $\chi^2_{1/f}(\sigma,\rho)=\lambda_\rho^f(\sigma-\rho,\sigma-\rho)$. No normalization $f(1)=1$ is imposed. The finite-parameter measure $\nu_f$ is determined by $1/f(t)=a_f+\int_{[0,\infty)}(s+t)^{-1}\,d\nu_f(s)$, with $a_f\ge0$.
--
--   Let $\rho$ be a faithful density and $x=x^*\in A$ with $\operatorname{Tr}x=0$. Let $\mathcal S_{\rho,x}=\{\rho+ux:u\in\mathbb R,\ \rho+ux\text{ is a density}\}$, including boundary states, and assume $T(\rho)>0$ and both $T^*$ and the computed dual $T_\rho(a)=T(\rho)^{-1/2}T(\rho^{1/2}a\rho^{1/2})T(\rho)^{-1/2}$ are unital Schwarz maps. The following five conditions are equivalent:
--
--   1. Some monotone metric is preserved at $x$ and $|\operatorname{supp}\nu_f|\ge|\operatorname{spec}(\Delta_\rho)\cup\operatorname{spec}(\Delta_{T(\rho)})|$.
--   2. For every real $t$,
--   $$
--   \rho^{it}x\rho^{-it-1}=T^*(T(\rho)^{it}T(x)T(\rho)^{-it-1}).
--   $$
--   3. $\rho^{-1/2}x\rho^{-1/2}=T^*(T(\rho)^{-1/2}T(x)T(\rho)^{-1/2})$.
--   4. $T$ is reversible for the entire maximal affine family $\mathcal S_{\rho,x}$.
--   5. $\lambda_\rho^f(x,x)=\lambda_{T(\rho)}^f(T(x),T(x))$ for every monotone metric.
--
--   The spectrum is that of the modular operator on the actual algebra, and the union counts distinct values.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 24, Proposition 4

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P31

open Filter MeasureTheory Set

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE)

open QAlgorithms.Papers.Independent.Dependency50.P21
  (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports matrixCommutant)

open QAlgorithms.Papers.Independent.Support50.P12
  (Alg AlgebraDensity AlgebraExtension PositiveOnConcreteAlgebra AlgebraTracePreserving
   AlgebraKPositive AlgebraCompletelyPositive supp spec cpow quasi hull modularSpec)

open QAlgorithms.Papers.Independent.Information100.P50 (OperatorMonotone)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- PDF p.24, Proposition 4: all FIVE criteria on the maximal affine state family.
The support is nu_f, the finite Stieltjes measure of 1/f with constant separated;
the printed integral-only representation on p.23 is corrected as documented. -/
theorem proposition4 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (rho x : Mat I) (hrho : AlgebraDensity A rho) (hfaith : rho.PosDef)
    (hx : Tangent A x) (h : Conditions A B T (affineFamily A rho x) rho) :
    List.TFAE [
      ∃ f : ℝ → ℝ, MetricGenerator f ∧
        MetricRich f ((modularSpec A rho rho ∪ modularSpec B (T rho) (T rho)).card) ∧
        metric f rho x x = metric f (T rho) (T x) (T x),
      ∀ t : ℝ, cpow rho (Complex.I * (t : ℂ)) * x * cpow rho (-Complex.I * (t : ℂ) - 1) =
        channelAdjoint T (cpow (T rho) (Complex.I * (t : ℂ)) * T x *
          cpow (T rho) (-Complex.I * (t : ℂ) - 1)),
      derivative x rho = channelAdjoint T (derivative (T x) (T rho)),
      FamilyReversible A B T (affineFamily A rho x),
      ∀ f : ℝ → ℝ, MetricGenerator f → metric f rho x x = metric f (T rho) (T x) (T x)] := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
