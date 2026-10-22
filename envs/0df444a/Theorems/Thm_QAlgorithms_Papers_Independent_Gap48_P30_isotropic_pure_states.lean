-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P30_isotropic_pure_states
-- name    : QAlgorithms.Papers.Independent.Gap48.P30.isotropic_pure_states
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:19:46.148819+00:00
-- url     : https://prove2.me/theorems/784425d5-c7ae-47b1-a533-3f3f4fd072ab
-- title:
--   Pure isotropic input states are number states; conditional route to C2
-- statement:
--   Let $u$ be a norm-one vector in the full one-mode Fock space and $\rho_u=|u\rangle\langle u|$. Define isotropy by rotational invariance of its Wigner distribution, $W_{\rho_u}(e^{i\theta}\alpha)=W_{\rho_u}(\alpha)$ for every real $\theta$ and complex $\alpha$. Here $W_\rho(\alpha)=\frac2\pi\operatorname{Re}\operatorname{Tr}[D(2\alpha)\Pi\rho]$, $D$ is the Weyl displacement and $\Pi|n\rangle=(-1)^n|n\rangle$. With $R_\theta|n\rangle=e^{in\theta}|n\rangle$, one has
--
--   $$
--   \rho_u\text{ isotropic}\ \Longleftrightarrow\ \forall\theta,\ R_\theta\rho_uR_\theta^*=\rho_u
--   \ \Longleftrightarrow\ \exists k\ge0,\ \rho_u=|k\rangle\langle k|.
--   $$
--
--   Every such vector is centered, meaning its annihilation-expectation series converges to zero. The Weyl, parity and phase-rotation operators in these criteria are realized bounded operators, and rotations are unitary.
--
--   For each amplifier gain $G\ge1$, if there exists a centered pure isotropic input attaining the minimum output entropy over centered pure inputs, then the vacuum also attains this minimum. This implication does not assert existence or isotropy of any optimizer.
--
--   This is the conditional isotropy route to C2. Density invariance allows the physically irrelevant phase acquired by a number-state vector.
-- source:
--   Majorization theory approach to the Gaussian channel minimum entropy conjecture, arXiv:1111.1986v1, PDF p. 3, Isotropy paragraph after (14)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P30

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- arXiv:1111.1986v1, PDF pp.3-4. A pure isotropic state is a number-state
density, not a vector fixed by every rotation. Isotropy uses the actual Wigner
function; rotation-invariant density is concluded as an equivalent criterion.
The optimizer route is conditional and does not assert an optimizer exists. -/
theorem isotropic_pure_states :
    D.DisplacementRealized ∧
    D.HasFockMatrix parity (fun m n => if m = n then (-1 : ℂ) ^ n else 0) ∧
    (∀ theta : ℝ, D.HasFockMatrix (C.fockPhaseRotation theta)
      (fun m n => if m = n then Complex.exp (Complex.I * (theta * n : ℝ)) else 0) ∧
      (C.fockPhaseRotation theta).adjoint.comp (C.fockPhaseRotation theta) = 1 ∧
      (C.fockPhaseRotation theta).comp (C.fockPhaseRotation theta).adjoint = 1) ∧
    (∀ u : D.Fock, ‖u‖ = 1 →
      (Isotropic (C.pureState u) ↔
        ∀ theta : ℝ, C.conjugateBy (C.fockPhaseRotation theta) (C.pureState u) = C.pureState u) ∧
      (Isotropic (C.pureState u) ↔ ∃ k : ℕ, C.pureState u = D.fockDyad k k) ∧
      (Isotropic (C.pureState u) → ZeroMean u)) ∧
    (∀ G : ℝ, 1 ≤ G →
      (∃ u : D.Fock, ‖u‖ = 1 ∧ ZeroMean u ∧ Isotropic (C.pureState u) ∧
        ∀ v : D.Fock, ‖v‖ = 1 → ZeroMean v →
          C.fockEntropyNats (C.amplifier G (C.pureState u)) ≤
            C.fockEntropyNats (C.amplifier G (C.pureState v))) →
      ∀ v : D.Fock, ‖v‖ = 1 → ZeroMean v →
        C.fockEntropyNats (C.amplifier G (D.fockDyad 0 0)) ≤
          C.fockEntropyNats (C.amplifier G (C.pureState v))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P30

end
