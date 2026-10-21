-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P31_characteristicDynamics_L2Contraction
-- name    : QAlgorithms.Papers.Independent.Next46.P31.characteristicDynamics_L2Contraction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:32:59.408219+00:00
-- url     : https://prove2.me/theorems/e6173334-7418-44a8-b2b8-fac3a62f0c24
-- title:
--   Unnumbered Section 3 result: contraction of characteristic dynamics
-- statement:
--   Let $A$ be a real symmetric positive-semidefinite matrix in $(q,p)$ block order and let $\mu$ be a positive origin-symmetric Borel Lévy measure, with zero mass at the origin and $\int(|x|^2+|k|^2)\,d\mu(x,k)<\infty$; its total mass may be infinite. Let $\Gamma_t$ be the characteristic dynamics defined by $\varphi_T(q,p)=\operatorname{Tr}(W_{q,p}T)$ and
--
--   $$
--   \varphi_{\Gamma_t(T)}(q,p)=\exp\!\left(\int_0^t\left[-\tfrac12\langle(q+(t-s)p,p),A(q+(t-s)p,p)\rangle+\psi_\mu(q+(t-s)p,p)\right]ds\right)\varphi_T(q+tp,p),
--   $$
--
--   where $W_{q,p}f(x)=e^{ip\cdot(x-q/2)}f(x-q)$ and $\psi_\mu(q,p)=\int(\cos(q\cdot k+p\cdot x)-1)\,d\mu(x,k)$. Apply that same multiplier/shear formula to every complex $L^2(dq\,dp)$ function, not merely to quantum characteristic functions. It defines bounded complex-linear operators $G_t$ on the full space, and
--
--   $$
--   G_0=I,\qquad G_{s+t}=G_sG_t\quad(s,t\ge0),\qquad \|G_tf\|_2\le\|f\|_2\quad(t\ge0).
--   $$
--
--   The action agrees almost everywhere with the explicitly displayed formula. Thus these maps form a contraction semigroup on all of phase-space $L^2$.
-- source:
--   Decoherence rates for Galilean covariant dynamics, arXiv:0710.1344v2, PDF p. 14, Unnumbered Section 3 result: contraction of characteristic dynamics

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P31

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Next46.P31

open QAlgorithms.PeriodicSchrodinger (Position)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace)

/-- Clark, PDF p.14, unnumbered Section 3 assertion: the formula defines a
semigroup of contractions on the full L2 space. The actual bounded linear maps,
identity, semigroup law, norm bound, and agreement with (1.19) are conclusions. -/
theorem characteristicDynamics_L2Contraction {d : ℕ} (hd : 0 < d)
    (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (mu : Measure (PhasePoint d))
    (hnoise : FiniteVarianceLevyNoise A mu) :
    ∃ G : ℝ≥0 → (Lp ℂ 2 (volume : Measure (PhasePoint d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (PhasePoint d))),
      (∀ t f, (G t f : PhasePoint d → ℂ) =ᵐ[volume]
        characteristicEvolution A mu (t : ℝ) (f : PhasePoint d → ℂ)) ∧
      G 0 = ContinuousLinearMap.id ℂ _ ∧
      (∀ s t, G (s + t) = (G s).comp (G t)) ∧
      (∀ t f, ‖G t f‖ ≤ ‖f‖) := by sorry

end QAlgorithms.Papers.Independent.Next46.P31

end
