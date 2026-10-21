-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P06_shiftReset_standard_nonclosable
-- name    : QAlgorithms.Papers.Independent.Renew46.P06.shiftReset_standard_nonclosable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:45:41.576972+00:00
-- url     : https://prove2.me/theorems/acb42be3-bad8-4dad-848c-c52a7aed69ad
-- title:
--   Conservative standard shift reset with nonclosable boundary jumps
-- statement:
--   Let $H=L^2(\mathbb R_+)$ and let $\Omega$ be an arbitrary density operator. There exist a countable rebound factorization $\Omega=\sum_j|l_j\rangle\langle l_j|$, the left-shift evolution $S_t^0\rho=W_t\rho W_t^*$, and its actual minimal reset evolution $S_t$ with normal dual $T_t$. The factors have $\sum_j\|l_j\|^2<\infty$. On the full domain $H^1(\mathbb R_+)$, with its absolutely continuous boundary representative, set
--
--   $$
--   Kf=-f',\qquad L_jf=f(0)l_j.
--   $$
--
--   These operators give a standard minimal realization. Its actual generators satisfy
--
--   $$
--   \operatorname{dom}G=\operatorname{dom}G_0,\qquad
--   G\rho=G_0\rho-\operatorname{Tr}(G_0\rho)\Omega,
--   \qquad -\operatorname{Tr}(G_0\rho)=\rho(0,0).
--   $$
--
--   The last value is the continuous boundary value of the nuclear diagonal density. For every $t\ge0$ and trace-class $\rho$, $\operatorname{Tr}(S_t\rho)=\operatorname{Tr}\rho$, and $T_t(I)=I$. Every $L_j$ with $l_j\ne0$ is nonclosable as a densely defined operator in $L^2$; its graph closure has a nonzero vector over zero. No boundary condition $f(0)=0$ is imposed on $H^1$.
--
--   This construction works for every rebound density. **Source correction:** the nonzero qualification is necessary because a zero spectral factor gives the closable zero jump.
-- source:
--   On singular perturbations of quantum dynamical semigroups, arXiv:1706.04866v5, PDF p. 4, §2, unnumbered result: standard conservative reset with nonclosable jumps

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

/-- PDF pp.3–4, (7)–(9): the actual minimal shift reset for arbitrary density Omega.
The printed nonclosability claim is qualified by l_j != 0: a padded zero jump is closable.
The representation uses the full H1 domain, K=-d/dx and L_j f=l_j f(0). -/
theorem shiftReset_standard_nonclosable (b : HilbertBasis ℕ ℂ HalfLine)
    (Omega : State b) :
    ∃ (l : ℕ → HalfLine) (W : ContractionSemigroup HalfLine) (Szero : TraceEvolution b) (Tzero : Evolution)
      (P : DomainPerturbation Szero) (S : TraceEvolution b) (T : Evolution),
      IsReboundDecomposition b Omega l ∧ IsLeftShift W ∧ IsShiftPair b W Szero Tzero ∧
      IsResetConstruction b Szero Omega P S T ∧
      TraceGeneratorDomain S = TraceGeneratorDomain Szero ∧
      ResetGeneratorFormula b Szero S Omega ∧
      (∀ rho eta : (TraceClass HalfLine), InTraceGeneratorGraph Szero rho eta →
        HasDiagonalBoundary rho (-(operatorTrace b eta.val))) ∧
      IsUnitalQDS T ∧
      (∀ t rho, operatorTrace b (S.maps t rho).val = operatorTrace b rho.val) ∧
      (∃ R : StandardRepresentation T,
        (R.D : Set HalfLine) = h1Domain ∧
        ∀ f : R.D, ∃ a : ℂ, H1Trace (f : HalfLine) (-(R.K f)) a ∧
          ∀ j, R.L j f = a • l j) ∧
      (∀ j, l j ≠ 0 → IsNonclosableGraph (boundaryJumpGraph (l j))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P06

end
