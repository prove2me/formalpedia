-- Prove2me | Theorems.Thm_PadicInt_KummerCarrier_evalAt_bijective_convHom
-- name    : PadicInt.KummerCarrier.evalAt_bijective_convHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/219261bb-4a8c-5009-8916-293ccb9f811f
-- title:
--   Evaluation maps: bijective convolution homomorphism (ℤ/p)²→ points
-- statement:
--   Fix a prime $p$ (as a natural number with the primality fact available) and a unit $u \in \mathbb{Z}_p^{\times}$, and work over the algebraic closure $\overline{\mathbb{Q}_p}$. Let $\zeta \in \overline{\mathbb{Q}_p}$ be a primitive $p$-th root of unity and let $\eta \in \overline{\mathbb{Q}_p}$ satisfy $\eta^p = u$, the image of $u$ under the structure map $\mathbb{Z}_p \to \overline{\mathbb{Q}_p}$. The assertion is the existence of a map $\psi_0 \colon \mathbb{Z}/p \times \mathbb{Z}/p \to \mathrm{Hom}_{\mathbb{Z}_p\text{-alg}}(\mathrm{Carrier}\,p\,u,\ \overline{\mathbb{Q}_p})$, where `Carrier p u` is the product over $j \in \mathbb{Z}/p$ of the algebras $\mathbb{Z}_p[X]/(X^p - u^{j.val})$, with three properties. First, $\psi_0$ is bijective onto the whole type of $\mathbb{Z}_p$-algebra homomorphisms `Carrier p u →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]`. Second, for all $i, j \in \mathbb{Z}/p$ the element $w = \zeta^{i.val}\eta^{j.val}$ satisfies $w^p = u^{j.val}$ in $\overline{\mathbb{Q}_p}$ and $\psi_0(i,j) =$ `evalAt p u j w`, namely the projection onto the $j$-th factor followed by the `AdjoinRoot` lift of `kpoly p u j` $= X^p - u^{j.val}$ that sends the canonical root to $w$. Third, $\psi_0$ is a homomorphism for convolution: for all $a, b \in \mathbb{Z}/p \times \mathbb{Z}/p$, the comultiplication `Δ p u` followed by `Algebra.TensorProduct.map (ψ₀ a) (ψ₀ b)` and then by multiplication `Algebra.TensorProduct.lmul'` on $\overline{\mathbb{Q}_p} \otimes_{\mathbb{Z}_p} \overline{\mathbb{Q}_p}$ equals $\psi_0(a+b)$.
--
--   This is the points-level description of the Kummer–Oort–Tate group scheme attached to $u$: its $\overline{\mathbb{Q}_p}$-points, taken with the convolution product coming from the comultiplication `Δ p u`, are identified with $\mathbb{Z}/p \times \mathbb{Z}/p$ via $(i,j) \mapsto$ evaluation at $\zeta^{i}\eta^{j}$ on the $j$-th component, the group law being stated directly as the displayed identity rather than through a bialgebra structure. It feeds the construction of the finite flat Kummer–Hopf algebra with its convolution structure, [`PadicInt.exists_finiteFlat_kummerHopf_withConv_aeval`](thm.html#PadicInt.exists_finiteFlat_kummerHopf_withConv_aeval).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_KummerCarrier_evalAt_bijective_convHom.lean

import Mathlib
import Definitions.Def_PadicInt_KummerCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct in
open PadicInt.KummerCarrier in

theorem PadicInt.KummerCarrier.evalAt_bijective_convHom
    (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ)
    (ζ η : AlgebraicClosure ℚ_[p]) (hζ : IsPrimitiveRoot ζ p)
    (hη : η ^ p = algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) (u : ℤ_[p])) :
    ∃ ψ₀ : ZMod p × ZMod p → (Carrier p u →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]),
      Function.Bijective ψ₀ ∧
      (∀ i j : ZMod p, ∃ hw, ψ₀ (i, j) = evalAt p u j (ζ ^ i.val * η ^ j.val) hw) ∧
      ∀ a b : ZMod p × ZMod p,
        (Algebra.TensorProduct.lmul' ℤ_[p] (S := AlgebraicClosure ℚ_[p])).comp
          ((Algebra.TensorProduct.map (ψ₀ a) (ψ₀ b)).comp (Δ p u))
          = ψ₀ (a + b) := by sorry
