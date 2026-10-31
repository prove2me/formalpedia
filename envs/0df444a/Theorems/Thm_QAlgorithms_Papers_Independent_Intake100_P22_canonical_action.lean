-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_canonical_action
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.canonical_action
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:33:14.7442+00:00
-- url     : https://prove2.me/theorems/0b672ef2-4b8a-4867-8b13-921fe25f7cba
-- title:
--   Canonical rotations, symbol substitution, and Gaussian kernel
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   For every $R\in SO(2n)$ there is a real skew matrix $H$ such that the unitary $V=e^{i\widehat H}$, with $\widehat H=(i/4)\sum_{a,b}H_{ab}c_ac_b$, satisfies $Vc_aV^\dagger=\sum_bR_{ab}c_b$. Every canonical $V$ implementing this same rotation obeys, for every $X$,
--   $$
--   \omega(VXV^\dagger,\theta)=\omega(X,R\theta),\qquad (A,B,D,C)=(0,R^T,0,1).
--   $$
--   Here the tuple specifies the Gaussian integral kernel of Definition 3. If $\rho$ has real covariance $M$, its transformed density has covariance
--   $$
--   M'=R^TMR.
--   $$
--   This identifies canonical FLO evolution with substitution of Grassmann variables.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 2, §II/IV/VI, Eqs.(5),(16): canonical transformations and their Gaussian kernel

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2,4,8, Eqs.(5),(16): every special orthogonal rotation is
implemented by exactly exp(iH) from Eq.(4); all implementations have B=R^T.
The covariance is R^T M R for the source's V c V-dagger convention. -/
theorem canonical_action {n : ℕ} (s : CARSystem n)
    (R : Matrix (Major n) (Major n) ℝ) (hR : Rotation R) :
    (∃ H : Matrix (Major n) (Major n) ℝ, H.transpose = -H ∧
      (canonicalFLO s H)ᴴ * canonicalFLO s H = 1 ∧
      canonicalFLO s H * (canonicalFLO s H)ᴴ = 1 ∧
      ImplementsRotation s (canonicalFLO s H) R) ∧
    (∀ V : Op (Qubits n), IsCanonicalFLO s V → ImplementsRotation s V R →
      HasGrassmannKernel s (conjSuperop V) (homogeneousKernel (R.transpose.map Complex.ofReal)) ∧
      (∀ X : Op (Qubits n), majoranaSymbol s (conjSuperop V X) =
        grassSubst (majoranaSymbol s X) (fun a =>
          ∑ b : Major n, (R a b : ℂ) • grassVar (2 * n) b.val)) ∧
      (∀ rho M, StateWith s rho M →
        StateWith s (conjSuperop V rho) (R.transpose * M * R))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
