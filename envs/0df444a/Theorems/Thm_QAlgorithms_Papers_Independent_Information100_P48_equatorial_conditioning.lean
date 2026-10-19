-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P48_equatorial_conditioning
-- name    : QAlgorithms.Papers.Independent.Information100.P48.equatorial_conditioning
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:47:38.53754+00:00
-- url     : https://prove2.me/theorems/81ca492a-e2db-47d8-9e0b-92b465296d15
-- title:
--   Equatorial branchwise uniformity and basis-independent marginal success
-- statement:
--   Let $\gamma\in[0,1]$ and let $\mathbf a=(a_x,a_y,a_z)$ be any unit Bloch direction. For outcome $s\in\{+1,-1\}$, Alice's normalized postmeasurement state from $I/2$ is $M_s=(I+s\,\mathbf a\cdot\boldsymbol\sigma)/2$. For the two concrete coherent ADC $+$ maps, success conditioned on this recorded outcome is
--
--   $$
--   p^{\rm ind}(s,\mathbf a)=1-\frac\gamma4+\frac{s\gamma a_z}{4},\qquad
--   p^D(s,\mathbf a)=1-\frac\gamma2+\frac{s\gamma a_z}{2}.
--   $$
--
--   For equatorial directions $a_z=0$, these are uniformly $1-\gamma/4$ and $1-\gamma/2$. For every unit direction, averaging the two outcomes with weights $1/2$ gives the corresponding marginal success $\operatorname{Tr}\Phi_+(I/2)$, independent of the axis. For the $Z$ direction, the two branchwise probabilities agree exactly when $\gamma=0$. This isolates the branchwise meaning of the source's non-uniform conditioning claim from its always basis-independent marginal.
-- source:
--   Coherent Control of Channel Dilations Activate Temporal Bell Nonclassicality, arXiv:2607.05643v1, PDF p. 12, Appendix A final paragraph: equatorial success versus outcome/axis-dependent conditioning

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate

noncomputable section

/-- Appendix A final paragraph, PDF pp.9,12: branchwise success is uniform in the
XY plane and generally differs between recorded Z outcomes. Correction of an
ambiguity: success marginalized over Alice's outcomes is basis-independent in
all planes, including XZ. No equality of the two normalization rules is assumed. -/
theorem equatorial_conditioning (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    (∀ a : Fin 3 → ℝ, UnitDirection a → ∀ minus : Bool,
      branchSuccess (independentADC g false) a minus =
        1 - g / 4 + outcomeSign minus * g / 4 * a 2 ∧
      branchSuccess (sharedADC g false) a minus =
        1 - g / 2 + outcomeSign minus * g / 2 * a 2) ∧
    (∀ a : Fin 3 → ℝ, UnitDirection a → a 2 = 0 → ∀ minus : Bool,
      branchSuccess (independentADC g false) a minus = 1 - g / 4 ∧
      branchSuccess (sharedADC g false) a minus = 1 - g / 2) ∧
    (∀ a : Fin 3 → ℝ, UnitDirection a →
      (branchSuccess (independentADC g false) a false +
        branchSuccess (independentADC g false) a true) / 2 =
          success (independentADC g false) ∧
      (branchSuccess (sharedADC g false) a false +
        branchSuccess (sharedADC g false) a true) / 2 = success (sharedADC g false)) ∧
    ((branchSuccess (independentADC g false) ![0, 0, 1] false =
      branchSuccess (independentADC g false) ![0, 0, 1] true) ↔ g = 0) ∧
    ((branchSuccess (sharedADC g false) ![0, 0, 1] false =
      branchSuccess (sharedADC g false) ![0, 0, 1] true) ↔ g = 0) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P48
