-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_tateParameter_of_prime_dvd_discr
-- name    : WeierstrassCurve.exists_tateParameter_of_prime_dvd_discr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/dd92fe5b-86d1-5f82-b2f1-afa6ab640e67
-- title:
--   Tate parameter at a prime of multiplicative reduction
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ (a tuple $(a_1,a_2,a_3,a_4,a_6)$ of integers) and let $\ell$ be a prime. Assume $\Delta(W)\neq 0$, $\ell \mid \Delta(W)$ and $\ell \nmid c_4(W)$. Then there exists $q_T \in \mathbb{Q}_\ell$ such that: $q_T \neq 0$; $\|q_T\| < 1$ (as an element of $\mathbb{R}_{\geq 0}$); the Weierstrass curve [`TateCurve.curve`](def/TateCurve_QSeries.html#L185) $q_T$, namely $y^2 + xy = x^3 + a_4(q_T)x + a_6(q_T)$ over $\mathbb{Q}_\ell$ with the coefficient series $a_4$, $a_6$ of the Tate curve, satisfies
--   $$c_4(\mathrm{curve}\,q_T)^3 = \iota\!\left(\frac{c_4(W_{\mathbb{Q}})^3}{\Delta(W_{\mathbb{Q}})}\right)\cdot \Delta(\mathrm{curve}\,q_T),$$
--   where $W_{\mathbb{Q}}$ is the base change of $W$ along $\mathbb{Z} \to \mathbb{Q}$, the quotient is formed in $\mathbb{Q}$ and $\iota : \mathbb{Q} \to \mathbb{Q}_\ell$ is the canonical map; and $\|q_T\| = \left(\ell^{\,v_\ell(\Delta(W))}\right)^{-1}$, with $v_\ell$ the $\ell$-adic valuation of the integer $\Delta(W)$. The third clause is the equality of $j$-invariants written multiplicatively, so as to avoid division.
--
--   This is Tate's $\ell$-adic uniformisation input in the form needed for an arbitrary integral Weierstrass model with multiplicative reduction at $\ell$: the $j$-invariant is then non-integral, and the associated Tate period $q_T$ has valuation equal to that of the discriminant of the model. It feeds the description of the $\ell$-torsion and of inertia at multiplicative primes, and the construction of finite flat prolongations of torsion at such primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_tateParameter_of_prime_dvd_discr.lean

import Mathlib
import Definitions.Def_TateCurve_QSeries
import Definitions.Def_TateCurve_TateParameter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal

theorem WeierstrassCurve.exists_tateParameter_of_prime_dvd_discr (W : WeierstrassCurve ℤ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hΔ : W.Δ ≠ 0) (hdvd : (ℓ : ℤ) ∣ W.Δ) (hndvd : ¬ (ℓ : ℤ) ∣ W.c₄) :
    ∃ qT : ℚ_[ℓ], qT ≠ 0 ∧ ‖qT‖₊ < 1 ∧
      (TateCurve.curve qT).c₄ ^ 3
        = (((W.map (Int.castRingHom ℚ)).c₄ ^ 3 / (W.map (Int.castRingHom ℚ)).Δ : ℚ) : ℚ_[ℓ])
            * (TateCurve.curve qT).Δ ∧
      ‖qT‖₊ = ((ℓ : ℝ≥0) ^ padicValInt ℓ W.Δ)⁻¹ := by sorry
