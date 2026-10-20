-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_basicProperties
-- name    : QAlgorithms.Papers.Independent.Information100.P08.basicProperties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:02:43.926028+00:00
-- url     : https://prove2.me/theorems/d85c99ff-f8be-4852-80df-8d0881f98eae
-- title:
--   Proposition 5.2: basic properties
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For a channel $\mathcal N:A\to B$ and input state $\tau$, let $f_{\mathcal N}(\tau)$ be the entanglement of formation of its reference–output state obtained from a purification of $\tau$. For a finite ensemble $e=(p_x,\tau_x)_x$, write $\bar\tau=\sum_xp_x\tau_x$ and $F_{\mathcal N}(e)=S(\mathcal N(\bar\tau))-\sum_xp_xS(\mathcal N(\tau_x))+\sum_xp_x f_{\mathcal N}(\tau_x)$. Define $U_F(\mathcal N)=\sup_e F_{\mathcal N}(e)$, allowing mixed ensemble members. Let $\chi(\mathcal N)$ be the supremum of output Holevo information over finite input ensembles. Then $$\max\{\chi(\mathcal N),\sup_\tau f_{\mathcal N}(\tau)\}\le U_F(\mathcal N)\le\sup_\tau S(\mathcal N(\tau)),\qquad U_F(\mathcal N)\le\log_2d_A.$$ For every channel $\mathcal M$ on its output, $U_F(\mathcal M\circ\mathcal N)\le U_F(\mathcal N)$. For every channel $\mathcal L:A\to B$ and $t\in[0,1]$, $$U_F((1-t)\mathcal N+t\mathcal L)\le(1-t)U_F(\mathcal N)+tU_F(\mathcal L).$$ These clauses concern the upper bound itself.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 22, Proposition 5.2: basic properties

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF p.22, Proposition 5.2: all basic inequalities, output processing, input-dimension
bound, and convexity of U_F. No operational-capacity convexity is asserted. -/
theorem basicProperties {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (N : Superop (Fin a) (Fin b)) (hN : IsChannel N) :
    max (channelHolevo N)
      (sSup {r | ∃ rho : Matrix (Fin a) (Fin a) ℂ, IsDensityMatrix rho ∧ r = channelFormation N rho})
      ≤ channelPotential N ∧
    channelPotential N ≤
      sSup {r | ∃ rho : Matrix (Fin a) (Fin a) ℂ, IsDensityMatrix rho ∧ r = vnEntropy (N rho)} ∧
    (∀ c : ℕ, 0 < c → ∀ M : Superop (Fin b) (Fin c), IsChannel M →
      channelPotential (M ∘ N) ≤ channelPotential N) ∧
    channelPotential N ≤ Real.logb 2 a ∧
    (∀ M : Superop (Fin a) (Fin b), IsChannel M → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      channelPotential (fun X => (1 - t) • N X + t • M X) ≤
        (1 - t) * channelPotential N + t * channelPotential M) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
