-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_winterYang
-- name    : QAlgorithms.Papers.Independent.Information100.P08.winterYang
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:01:24.618558+00:00
-- url     : https://prove2.me/theorems/63561c12-9559-4332-86d2-ae96b0dd3893
-- title:
--   Proposition 5.1: Winter–Yang expression
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For a channel $\mathcal N:A\to B$ and input state $\tau$, let $f_{\mathcal N}(\tau)$ be the entanglement of formation of its reference–output state obtained from a purification of $\tau$. For a finite ensemble $e=(p_x,\tau_x)_x$, write $\bar\tau=\sum_xp_x\tau_x$ and $F_{\mathcal N}(e)=S(\mathcal N(\bar\tau))-\sum_xp_xS(\mathcal N(\tau_x))+\sum_xp_x f_{\mathcal N}(\tau_x)$. Define $U_F(\mathcal N)=\sup_e F_{\mathcal N}(e)$, allowing mixed ensemble members. For a state $\sigma_{BE}$, $J(E;B)_\sigma$ is the supremum of outcome–$B$ mutual information over finite POVMs on $E$, and $G_E(\sigma)$ is its convex roof over decompositions into possibly mixed states. Let $V:A\to B\otimes E$ be any isometric Stinespring extension, so that $\operatorname{Tr}_E(V\tau V^\dagger)=\mathcal N(\tau)$. Then $$U_F(\mathcal N)=\sup_{\tau\in\mathcal S(A)}\{S(\mathcal N(\tau))-G_E(V\tau V^\dagger)\}.$$ This identifies the mathematical mixed-roof expression; it does not identify it with an operational potential capacity.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 21, Proposition 5.1: Winter–Yang expression

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF pp.21-22, Proposition 5.1: G measures E and allows mixed components. -/
theorem winterYang {a b e : ℕ} (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (N : Superop (Fin a) (Fin b)) (hN : IsChannel N)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : Vᴴ * V = 1)
    (hExtension : ∀ X, traceRight (V * X * Vᴴ) = N X) :
    channelPotential N = sSup {r | ∃ rho : Matrix (Fin a) (Fin a) ℂ,
      IsDensityMatrix rho ∧ r = vnEntropy (N rho) - environmentRoof (V * rho * Vᴴ)} := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
