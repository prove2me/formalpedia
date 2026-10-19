-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P10_twirl_invariance
-- name    : QAlgorithms.Papers.Independent.Independent1.P10.twirl_invariance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:27:03.598703+00:00
-- url     : https://prove2.me/theorems/c3dbf949-68aa-4343-95fa-5af2fd0337b9
-- title:
--   Twirling preserves the channel, its fidelities, and unitary covariance
-- statement:
--   Let $d>0$ and let $\mathcal E$ be a completely positive trace-preserving map. Define its normalized unitary Haar twirl by $\mathcal E_T(X)=\int U^\dagger\mathcal E(UXU^\dagger)U\,dU$. Then $\mathcal E_T$ is completely positive and trace preserving, and
--
--   $$\overline F(\mathcal E_T)=\overline F(\mathcal E),\qquad F_e(\mathcal E_T)=F_e(\mathcal E),\qquad V\mathcal E_T(\rho)V^\dagger=\mathcal E_T(V\rho V^\dagger)$$
--
--   for every density matrix $\rho$ and unitary $V$. Here $\overline F$ is the normalized pure-state Haar overlap average, and $F_e$ is the normalized maximally entangled overlap with identity action on the reference register.
--
--   These properties allow the fidelity calculation to be reduced to a unitarily covariant channel.
-- source:
--   A simple formula for the average gate fidelity of a quantum dynamical operation, arXiv:quant-ph/0205035v2, Twirled channel: channel property, fidelity invariance, and unitary covariance; Eqs. (6), (8), (10), PDF p. 1. https://arxiv.org/abs/quant-ph/0205035v2 . PDF SHA-256: a59643207560eeaa2b638e69af6528c299e929c2eab2af32f0117a5d6a2f2f2a.

import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P10_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P10












/-- Nielsen, PDF pp.1--2, Eqs. (6), (8), (10): the computed twirl is a channel,
preserves both fidelities, and is covariant on all density inputs. -/
theorem twirl_invariance (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) :
    IsChannel (QuditFidelity.haarTwirl d hd E) ∧
    QuditFidelity.averageFidelity d hd (QuditFidelity.haarTwirl d hd E) =
      QuditFidelity.averageFidelity d hd E ∧
    QuditFidelity.entanglementFidelity d hd (QuditFidelity.haarTwirl d hd E) =
      QuditFidelity.entanglementFidelity d hd E ∧
    ∀ (rho : Matrix (Fin d) (Fin d) ℂ), IsDensityMatrix rho →
      ∀ V : Matrix.unitaryGroup (Fin d) ℂ,
        conjSuperop (V : Matrix (Fin d) (Fin d) ℂ) (QuditFidelity.haarTwirl d hd E rho) =
          QuditFidelity.haarTwirl d hd E (conjSuperop (V : Matrix (Fin d) (Fin d) ℂ) rho) := by sorry






end QAlgorithms.Papers.Independent.Independent1.P10
