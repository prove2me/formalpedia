-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P04_auxiliaryRegularization
-- name    : QAlgorithms.Papers.Independent.Information100.P04.auxiliaryRegularization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:30:51.56298+00:00
-- url     : https://prove2.me/theorems/2883a45b-91d9-4dde-8094-0fa38174f9a4
-- title:
--   Auxiliary operational regularization and PPT monotonicity
-- statement:
--   For a bipartite density matrix $\rho$ on nonzero finite-dimensional systems, let $\widetilde L$ denote the supremum of the absolute-operator measurement score (35), and let $L$ denote (9). Then
--
--   $$\lim_{n\to\infty}\frac{\widetilde L(\rho^{\otimes n})}{n}=E_{d,\mathrm{PPT}}(\rho),\qquad \widetilde L(\rho)\le E_{d,\mathrm{PPT}}(\rho).$$
--
--   For every PPT channel $\Lambda$, both normalized level sequences at $\Lambda(\rho)$ converge to $E_{d,\mathrm{PPT}}(\Lambda(\rho))\le E_{d,\mathrm{PPT}}(\rho)$. Thus both regularized functionals are PPT monotones. This statement does not assume single-copy monotonicity of $\widetilde L$.
-- source:
--   On PPT entanglement distillation, arXiv:2610.12454v1, PDF p. 16, eq65

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P04

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Eq.(65), PDF p.16: the auxiliary regularization has the same operational value;
both regularizations are PPT monotones. -/
theorem auxiliaryRegularization {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) :
    Tendsto (LTildeLevel rho) atTop (nhds (distillable rho)) ∧ LTilde rho ≤ distillable rho ∧
    ∀ (C D : Type) [Fintype C] [Fintype D] [DecidableEq C] [DecidableEq D]
      [Nonempty C] [Nonempty D] (Phi : Superop (A × B) (C × D)), IsPPTChannel Phi →
      Tendsto (LLevel (Phi rho)) atTop (nhds (distillable (Phi rho))) ∧
      Tendsto (LTildeLevel (Phi rho)) atTop (nhds (distillable (Phi rho))) ∧
      distillable (Phi rho) ≤ distillable rho := by sorry

end QAlgorithms.Papers.Independent.Information100.P04

end
