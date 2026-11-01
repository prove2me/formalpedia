-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P10_pureOutput_poor_inequality_fails
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P10.pureOutput_poor_inequality_fails
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:41:54.258421+00:00
-- url     : https://prove2.me/theorems/5f5de782-1c7c-4c9a-88b8-40c27ba9ca73
-- title:
--   Strict obstruction to the classical poor-channel inequality
-- statement:
--   Let $W$ have two normalized pure outputs on a finite nonempty register, with squared overlap strictly between zero and one. Construct $W^-$ from the even and odd parity mixtures in Appendix A. Write $f=\sqrt{F(W)}$. Then
--
--   $$
--   \sqrt{F(W^-)}=f<f\sqrt{2-f^2}.
--   $$
--
--   Thus the lower bound in (10), valid for commuting-output channels, fails strictly here. This statement concerns that inequality and does not assert unattainability of a private information rate.
-- source:
--   Polar codes for degradable quantum channels, arXiv:1109.5346v3, PDF p. 5, §III/Appendix A, unnumbered obstruction to the classical poor-channel inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P10

open scoped BigOperators Matrix ComplexConjugate

open Filter

-- Accepted definitions, without paper-local aliases.

open QAlgorithms.Papers.Independent.Information100.P58 (basisDensity)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation)

/-- PDF pp.5,10: strict failure of the classical poor-channel inequality (10)
for pure outputs whose squared overlap is strictly between zero and one.
Only failure of that inequality is asserted, not an impossibility of private coding. -/
theorem pureOutput_poor_inequality_fails {H : Type*}
    [Fintype H] [DecidableEq H] [Nonempty H]
    (psi0 psi1 : EuclideanSpace ℂ H) (h0 : IsState psi0) (h1 : IsState psi1)
    (hlo : 0 < ‖inner ℂ psi0 psi1‖ ^ 2) (hhi : ‖inner ℂ psi0 psi1‖ ^ 2 < 1) :
    let W := pureCQ psi0 psi1
    let M := minusChannel W
    let f := rootFidelity (W false) (W true)
    rootFidelity (M false) (M true) = f ∧
      rootFidelity (M false) (M true) < f * Real.sqrt (2 - f ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P10

end
