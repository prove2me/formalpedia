-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_exactAmortization
-- name    : QAlgorithms.Papers.Independent.Information100.P08.exactAmortization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:00:08.613879+00:00
-- url     : https://prove2.me/theorems/c64cb9c1-fc59-461b-8514-b8876f9cc356
-- title:
--   Theorem 4.2: exact potential amortization
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For a channel $\mathcal N:A\to B$ and input state $\tau$, let $f_{\mathcal N}(\tau)$ be the entanglement of formation of its reference–output state obtained from a purification of $\tau$. For a finite ensemble $e=(p_x,\tau_x)_x$, write $\bar\tau=\sum_xp_x\tau_x$ and $F_{\mathcal N}(e)=S(\mathcal N(\bar\tau))-\sum_xp_xS(\mathcal N(\tau_x))+\sum_xp_x f_{\mathcal N}(\tau_x)$. Define $U_F(\mathcal N)=\sup_e F_{\mathcal N}(e)$, allowing mixed ensemble members. Let $\rho_{WA^{\prime}AB^{\prime}}=\sum_wp_w\lvert w\rangle\langle w\rvert\otimes\rho^w$ be any finite cq state, with arbitrary distribution and mixed conditionals. Apply $\mathcal N$ only to $A$, obtaining $\omega$. Define $\Delta Q=I(W;B^{\prime}B)_\omega+\sum_wp_wE_F(A^{\prime};B^{\prime}B)_{\omega^w}-I(W;B^{\prime})_\rho-\sum_wp_wE_F(A^{\prime}A;B^{\prime})_{\rho^w}$. Then $$\Delta Q\le U_F(\mathcal N),\qquad\sup_{A^{\prime},B^{\prime},\rho}\Delta Q=U_F(\mathcal N).$$ The supremum ranges over all finite memories and cq inputs. This is exact potential amortization, not an operational coding-rate equality.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 16, Theorem 4.2: exact potential amortization

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF pp.16-18, Theorem 4.2: arbitrary mixed cq inputs and memories, and exact optimized equality. -/
theorem exactAmortization {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (N : Superop (Fin a) (Fin b)) (hN : IsChannel N) :
    (∀ c d : ℕ, 0 < c → 0 < d → ∀ e : Ensemble ((Fin c × Fin a) × Fin d),
      potentialIncrement N e ≤ channelPotential N) ∧
    amortizedPotential N = channelPotential N := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
