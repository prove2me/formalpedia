-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_continuousOneShotSDP
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.continuousOneShotSDP
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:33:30.610517+00:00
-- url     : https://prove2.me/theorems/dc3e7a12-fc56-4cac-a780-edff1bb0b45c
-- title:
--   Theorem 4: continuous one-shot error-capacity SDPs
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on nonzero finite complex registers, and let $0\le e<1$. For $\Omega=\mathrm{NS}$ or $\mathrm{NS}\cap\mathrm{PPT}$, define $C^{(1)}_\Omega(\mathcal N,e)$ using the continuous success-SDP extension to real message parameter $\lambda\ge1$. Then
--
--   $$C^{(1)}_\Omega(\mathcal N,e)=-\log_2\min\eta,$$
--
--   subject to $\rho\succeq0$, $\operatorname{Tr}\rho=1$, $0\preceq F\preceq\rho\otimes I_B$, $\operatorname{Tr}_AF=\eta I_B$, and $\operatorname{Tr}(J_\mathcal NF)\ge1-e$. For NS∩PPT also require $0\preceq F^{T_B}\preceq\rho\otimes I_B$. The minimum is attained and positive. This quantity is a continuous relaxation of the operational integer-message one-shot capacity.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 9, Theorem 4

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P23

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (log2 quantumCapacity)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- PDF pp.9–10, Theorem 4: the continuous one-shot capacities, not the integer
operational capacities. The eta minimum is attained and strictly positive for e<1. -/
theorem continuousOneShotSDP [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (e : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) :
    ∀ ppt : Bool,
      IsLeast (etaValues ppt N e) (sInf (etaValues ppt N e)) ∧
      0 < sInf (etaValues ppt N e) ∧
      oneShot ppt N e = -log2 (sInf (etaValues ppt N e)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
