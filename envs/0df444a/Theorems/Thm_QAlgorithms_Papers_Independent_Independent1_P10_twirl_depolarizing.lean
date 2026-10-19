-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P10_twirl_depolarizing
-- name    : QAlgorithms.Papers.Independent.Independent1.P10.twirl_depolarizing
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:27:11.410227+00:00
-- url     : https://prove2.me/theorems/0773962e-be0f-440d-bf6c-92288ff54378
-- title:
--   The unitary Haar twirl is depolarizing
-- statement:
--   Let $d>0$ and let $\mathcal E$ be a completely positive trace-preserving map. Its normalized unitary Haar twirl $\mathcal E_T(X)=\int U^\dagger\mathcal E(UXU^\dagger)U\,dU$ has a real parameter $p$, independent of the density input, such that
--
--   $$\mathcal E_T(\rho)=\frac p d I+(1-p)\rho\qquad\text{for every density matrix }\rho.$$
--
--   No additional interval constraint on $p$ is imposed. This identifies the twirl as a depolarizing channel.
-- source:
--   A simple formula for the average gate fidelity of a quantum dynamical operation, arXiv:quant-ph/0205035v2, Unnumbered central proof result: the twirl is depolarizing, PDF p. 2. https://arxiv.org/abs/quant-ph/0205035v2 . PDF SHA-256: a59643207560eeaa2b638e69af6528c299e929c2eab2af32f0117a5d6a2f2f2a.

import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P10_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P10













/-- Nielsen, PDF p.2, central twirling argument: a single real depolarizing
parameter works for every density input. No interval restriction on p is asserted. -/
theorem twirl_depolarizing (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) :
    ∃ p : ℝ, ∀ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho →
      QuditFidelity.haarTwirl d hd E rho =
        ((p/(d : ℝ) : ℝ) : ℂ) • 1 + ((1-p : ℝ) : ℂ) • rho := by sorry





end QAlgorithms.Papers.Independent.Independent1.P10
