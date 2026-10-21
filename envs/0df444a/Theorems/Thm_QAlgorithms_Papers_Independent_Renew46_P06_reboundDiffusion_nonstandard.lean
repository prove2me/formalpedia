-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P06_reboundDiffusion_nonstandard
-- name    : QAlgorithms.Papers.Independent.Renew46.P06.reboundDiffusion_nonstandard
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:43:18.878813+00:00
-- url     : https://prove2.me/theorems/8ca2358f-b909-4bd9-9c3b-48a986d00712
-- title:
--   Rebound diffusion is conservative and nonstandard
-- statement:
--   Let $H=L^2(\mathbb R_+)$ and let $\Omega$ be any positive trace-class operator with $\operatorname{Tr}\Omega=1$. Put $D=H^2(\mathbb R_+)\cap H^1_0(\mathbb R_+)$, $K=-d^2/dx^2$ on its full domain $D$, and $L=\sqrt2\,d/dx$ on $D$. The minimal backward master equation defines a normal CP absorbing evolution $T_t^0$ and its trace-norm continuous predual $S_t^0$. This evolution is standard and nonconservative.
--
--   There exist the CP reset perturbation and its minimal evolution $S_t$, with normal dual $T_t$, satisfying
--
--   $$
--   \begin{aligned}
--   \operatorname{dom}G&=\operatorname{dom}G_0,\\
--   G\rho&=G_0\rho-\operatorname{Tr}(G_0\rho)\,\Omega,\\
--   \Lambda\rho&=\Omega\left.\frac{d}{dx}\rho(x,x)\right|_{0+}
--   =-\operatorname{Tr}(G_0\rho)\,\Omega,\\
--   \operatorname{Tr}(S_t\rho)&=\operatorname{Tr}\rho,\qquad T_t(I)=I,\\
--   T&\text{ is not standard.}
--   \end{aligned}
--   $$
--
--   Here $G_0$ and $G$ are the full actual trace-norm generators, $t\ge0$, and $\rho$ ranges over the complex trace class (over the generator domain in the generator formulas). The diagonal boundary derivative uses a differentiable representative of the nuclear diagonal density, vanishing at zero. Standardness means existence of any maximal accretive Hilbert generator and countably many jumps on any common dense invariant core, satisfying the dissipativity inequality and generating the evolution as the minimal backward solution. Its negation excludes every such representation. Neither contradiction lemma is an assumption.
--
--   This supplies the paper's concrete conservative evolution beyond the standard generator construction.
-- source:
--   On singular perturbations of quantum dynamical semigroups, arXiv:1706.04866v5, PDF p. 9, §3.2, unnumbered main result: the rebound diffusion is nonstandard

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P06

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Renew46.P06

open QAlgorithms.Papers.Independent.Dependency50.P13
  (TraceClass State NuclearRepresentation traceNormValue operatorTrace)

open QAlgorithms.Papers.Independent.Claimed50.P50
  (ContractionSemigroup DynamicalSemigroup IsCPOnBoundedOperators
    IsUnitalQDS IsRelaxingEvolution)

open QAlgorithms.Papers.Independent.Next46.P09
  (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain
    DomainPerturbation IsMinimalPerturbation)

/-- PDF pp.8–11, (19)–(20): existence of the actual absorbing and reset evolutions,
full generator/domain identification, conservativity of rebound, and nonstandardness
against EVERY admissible invariant-core representation. Lemmas 6 and 7 are not hypotheses. -/
theorem reboundDiffusion_nonstandard (b : HilbertBasis ℕ ℂ HalfLine) (Omega : State b) :
    ∃ (Tzero : Evolution) (Szero : TraceEvolution b)
      (P : DomainPerturbation Szero) (S : TraceEvolution b) (T : Evolution),
      IsAbsorbingDiffusion Tzero ∧ IsPredual b Szero Tzero ∧
      IsStandard Tzero ∧ ¬ IsUnitalQDS Tzero ∧
      IsResetConstruction b Szero Omega P S T ∧
      TraceGeneratorDomain S = TraceGeneratorDomain Szero ∧
      ResetGeneratorFormula b Szero S Omega ∧
      (∀ rho eta : (TraceClass HalfLine), InTraceGeneratorGraph Szero rho eta →
        HasBoundaryFlux rho (-(operatorTrace b eta.val))) ∧
      IsUnitalQDS T ∧
      (∀ t rho, operatorTrace b (S.maps t rho).val = operatorTrace b rho.val) ∧
      ¬ IsStandard T := by sorry

end QAlgorithms.Papers.Independent.Renew46.P06

end
