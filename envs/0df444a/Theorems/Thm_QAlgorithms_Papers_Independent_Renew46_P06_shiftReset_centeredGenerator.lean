-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P06_shiftReset_centeredGenerator
-- name    : QAlgorithms.Papers.Independent.Renew46.P06.shiftReset_centeredGenerator
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:48:19.086994+00:00
-- url     : https://prove2.me/theorems/15f358b4-893a-4145-952a-1a7fd0726379
-- title:
--   Centering a reset observable gives the unperturbed shift generator value
-- statement:
--   Let $\Omega$ be a density operator on $L^2(\mathbb R_+)$, let $\mathcal L$ be the ultraweak generator of the actual minimal reset shift, and let $\mathcal L_0$ be the unperturbed shift dual generator. If $X\in\operatorname{dom}\mathcal L$, define $X_0=X-\operatorname{Tr}(\Omega X)I$. Then
--
--   $$
--   X_0\in\operatorname{dom}\mathcal L_0,\qquad
--   \mathcal L_0(X_0)=\mathcal L(X).
--   $$
--
--   Equivalently, for the actual value $Y=\mathcal L(X)$, the pair $(X_0,Y)$ lies in the full ultraweak generator graph of the unperturbed evolution. The centered observable is computed from $X$ and $\Omega$.
--
--   This transfers both domain membership and the generator value; no converse domain equivalence is asserted.
-- source:
--   On singular perturbations of quantum dynamical semigroups, arXiv:1706.04866v5, PDF p. 5, Lemma 4: centered shift-reset observables lie in the unperturbed domain

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

/-- PDF pp.5–6, Lemma 4: X0 is computed from X and Omega; both membership and
actual generator value are retained. No converse domain assertion is added. -/
theorem shiftReset_centeredGenerator (b : HilbertBasis ℕ ℂ HalfLine)
    (Omega : State b) (W : ContractionSemigroup HalfLine) (hShift : IsLeftShift W)
    (Szero : TraceEvolution b) (Tzero : Evolution) (hPair : IsShiftPair b W Szero Tzero)
    (P : DomainPerturbation Szero) (S : TraceEvolution b) (T : Evolution)
    (hReset : IsResetConstruction b Szero Omega P S T)
    (X Y : (HalfLine →L[ℂ] HalfLine)) (hGenerator : InDualGeneratorGraph b T X Y) :
    let Xzero := X - operatorTrace b (Omega.val.val.comp X) • identityObservable
    Xzero ∈ dualGeneratorDomain b Tzero ∧ InDualGeneratorGraph b Tzero Xzero Y := by sorry

end QAlgorithms.Papers.Independent.Renew46.P06

end
