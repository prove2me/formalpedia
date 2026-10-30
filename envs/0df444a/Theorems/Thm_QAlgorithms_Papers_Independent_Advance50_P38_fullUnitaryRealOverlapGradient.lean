-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_fullUnitaryRealOverlapGradient
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.fullUnitaryRealOverlapGradient
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:49:44.185301+00:00
-- url     : https://prove2.me/theorems/a0a90d2e-2b60-418f-9528-ab37ccd4aa0e
-- title:
--   §III.D worked example: real-overlap gradient (104)–(109)
-- statement:
--   Let $N>0$ and let $A,C$ be arbitrary complex $N$ by $N$ matrices. Equip $\mathrm{SU}(N)$ with $\langle\Omega U,\Xi U\rangle_U=\operatorname{Re}\operatorname{tr}(\Omega^\dagger\Xi)$, where $\Omega,\Xi$ are skew-Hermitian and traceless. Write $B=UAU^\dagger$, $S(D)=(D-D^\dagger)/2$ and $f(U)=\operatorname{Re}\operatorname{tr}(C^\dagger B)$. Then
--   $$D(C^\dagger UAU^\dagger)[\Omega U]=C^\dagger\Omega B-C^\dagger B\Omega,\qquad \operatorname{grad}f(U)=-S([B,C^\dagger])U.$$
--   The displayed field is the unique tangent vector representing all directional derivatives under this metric. Its exponential step $U_+=\exp(-\alpha S([B,C^\dagger]))U$ belongs to $\mathrm{SU}(N)$ for $\alpha\ge0$ and has derivative equal to the gradient at $\alpha=0$. It gives the source's ascent system and exponential discretization. The exponent uses the correction specified in the formalization notes.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 20, §III.D worked example: real-overlap gradient (104)–(109)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Worked example (104)--(109), PDF p.20. The missing dagger in the
printed exponent (109) is repaired from (104)--(108) and Table II U1 (p.33). -/
theorem fullUnitaryRealOverlapGradient {n : ℕ} (hn : 0 < n) (A C : (Matrix (Fin n) (Fin n) ℂ))
    (U : Matrix.specialUnitaryGroup (Fin n) ℂ) :
    (∀ Omega : (Matrix (Fin n) (Fin n) ℂ), IsSpecialSkew Omega →
      HasDerivAt (fun t : ℝ => C.conjTranspose *
        ((NormedSpace.exp (t • Omega) * (U : (Matrix (Fin n) (Fin n) ℂ))) * A *
          (NormedSpace.exp (t • Omega) * (U : (Matrix (Fin n) (Fin n) ℂ))).conjTranspose))
        (C.conjTranspose * Omega * ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose) -
          C.conjTranspose * ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose) * Omega) 0) ∧
    IsSUGradient A C U (unitaryGradientField A C U) ∧
    (∀ V : (Matrix (Fin n) (Fin n) ℂ), IsSUGradient A C U V ↔ V = unitaryGradientField A C U) ∧
    (∀ a : ℝ, 0 ≤ a → unitaryAscentStep A C U a ∈ Matrix.specialUnitaryGroup (Fin n) ℂ) ∧
    HasDerivAt (unitaryAscentStep A C U) (unitaryGradientField A C U) 0 := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
