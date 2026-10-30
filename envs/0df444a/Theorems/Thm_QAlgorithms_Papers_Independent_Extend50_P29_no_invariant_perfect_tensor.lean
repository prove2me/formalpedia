-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P29_no_invariant_perfect_tensor
-- name    : QAlgorithms.Papers.Independent.Extend50.P29.no_invariant_perfect_tensor
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:12:59.334058+00:00
-- url     : https://prove2.me/theorems/480a70fb-07db-4e56-95a5-240b0cfe41cc
-- title:
--   Discussion: no nontrivially SU(2)-invariant perfect tensors with at least four equal-dimensional factors
-- statement:
--   Let $m\ge4$ and $d\ge2$. Let $U_j:SU(2)\to U(d)$ be continuous unitary representations on the $m$ equal-dimensional legs, and suppose at least one local conjugation action is nontrivial: $U_j(g)\rho U_j(g)^\dagger\ne\rho$ for some $j,g$ and density matrix $\rho$. Then no normalized vector $\psi\in(\mathbb C^d)^{\otimes m}$ is both invariant and perfect. In formulas there is no unit vector satisfying
--   $$\left(\bigotimes_{j=1}^m U_j(g)\right)\psi=\psi\quad(\forall g\in SU(2)),\qquad
--   \operatorname{Tr}_{R^{\rm c}}|\psi\rangle\langle\psi|=\frac{I_R}{d^{|R|}}\quad(2|R|\le m).$$
--   The marginal criterion expresses proportional-isometry flattenings of a normalized perfect tensor. It includes the four-leg case and the higher-leg consequence, and makes the implicit equal-dimension and nontrivial-action conventions explicit. For continuous finite-dimensional $SU(2)$ representations, nontrivial conjugation is equivalent to some nontrivial infinitesimal conjugation action.
-- source:
--   Error Correction of Quantum Reference Frame Information, arXiv:1709.04471v1, PDF p. 5, Discussion: no nontrivially SU(2)-invariant perfect tensors with at least four equal-dimensional factors

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P29

noncomputable section

open MeasureTheory MeasureTheory.Measure

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P29

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt rectAct)

open QAlgorithms.Papers.Independent.Support21.P09 (groupLeftRegular)

/-- PDF p.5, discussion: no SU(2)-invariant perfect tensor on at least four
equal-dimensional legs if a local continuous conjugation action is nontrivial.
This excludes trivial representations and the one-dimensional counterexample. -/
theorem no_invariant_perfect_tensor
    {m d : ℕ} (hm : 4 ≤ m) (hd : 2 ≤ d)
    (U : (j : Fin m) → Matrix.specialUnitaryGroup (Fin 2) ℂ →*
      Matrix.unitaryGroup (Fin d) ℂ)
    (hcU : ∀ j, Continuous (U j))
    (hNontrivial : ∃ j g ρ, IsDensityMatrix ρ ∧
      conjSuperop (U j g : Matrix (Fin d) (Fin d) ℂ) ρ ≠ ρ) :
    ¬ ∃ ψ : EuclideanSpace ℂ (Fin m → Fin d), PerfectTensor ψ ∧
      ∀ g, act (localTensorMatrix (fun j => (U j g : Matrix (Fin d) (Fin d) ℂ))) ψ = ψ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P29

end
