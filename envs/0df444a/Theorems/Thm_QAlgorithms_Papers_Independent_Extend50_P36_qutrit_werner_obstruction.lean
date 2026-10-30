-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_qutrit_werner_obstruction
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.qutrit_werner_obstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:10:59.974805+00:00
-- url     : https://prove2.me/theorems/defc9344-152f-47e4-95e1-1b2f61c51d55
-- title:
--   Sec. IV B, unnumbered: extremal qutrit Werner obstruction
-- statement:
--   Let $d\ge2$ be an integer. Write $\rho_W(\psi)$ for the $d$-dimensional Werner state with swap expectation $\psi\in[-1,1]$, and $\rho_I(\phi)$ for the isotropic state with $\phi=dF\in[0,d]$, where $F$ is its overlap with the normalized maximally entangled vector. A joining state is a positive semidefinite operator of trace one having the specified ordered pair marginals.For positive integers $m,n$, a state is $m$-$n$ sharable when a density operator on $H_L^{\otimes m}\otimes H_R^{\otimes n}$ has that same state as every left-right pair marginal. Arbitrary sharing means such an extension exists for every positive finite $m,n$.
--
--   In dimension three let $\rho=\rho_W(-1)$ and $w=|v_3\rangle\langle v_3|$, where $v_3$ is the normalized fully antisymmetric three-qutrit vector. Then
--   $$\rho\text{ is }1\text{-}2\text{ sharable but not }2\text{-}2\text{ sharable},\qquad \{X:X_{AB}=X_{AC}=\rho,\ X\text{ a density operator}\}=\{w\}.$$
--   The unique-extension assertion is a conclusion, as in the source.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 12, Sec. IV B, unnumbered: extremal qutrit Werner obstruction

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Sec.IV B, PDF p.12: the extremal qutrit Werner state is 1-2 but not 2-2
sharable, and its three-party joining state is uniquely the antisymmetric pure state. -/
theorem qutrit_werner_obstruction :
    Sharable 1 2 (wernerSwapState 3 (-1)) ∧ ¬ Sharable 2 2 (wernerSwapState 3 (-1)) ∧
    JoinsTwo (fun a b : Fin 3 × Fin 3 × Fin 3 =>
      pureDensity (fullAntisymmetricVector 3) ![a.1,a.2.1,a.2.2] ![b.1,b.2.1,b.2.2])
      (wernerSwapState 3 (-1)) (wernerSwapState 3 (-1)) ∧
    (∀ X : Op (Fin 3 × Fin 3 × Fin 3), JoinsTwo X (wernerSwapState 3 (-1)) (wernerSwapState 3 (-1)) →
      X = fun a b => pureDensity (fullAntisymmetricVector 3) ![a.1,a.2.1,a.2.2] ![b.1,b.2.1,b.2.2]) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
