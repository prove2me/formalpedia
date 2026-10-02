-- Prove2me | Theorems.Thm_StochFictPlay_DiscreteChoice_legendre_duality_strictlyConvex
-- name    : StochFictPlay.DiscreteChoice.legendre_duality_strictlyConvex
-- status  : Disproved
-- author  : @junyihjy
-- created : 2026-10-01T17:47:09.440426+00:00
-- url     : https://prove2.me/theorems/e8638dfb-c7e1-4eaa-993d-bff57bdf8bed
-- title:
--   Legendre duality for the SFP perturbation potential (Rockafellar Thm 26.5 instantiated; Hofbauer–Sandholm 2002, Thm 2.1)
-- statement:
--   Let W : (Fin n → ℝ) → ℝ be strictly convex and C¹ on an open set O (the tangent space R₀ⁿ), with gradient field C = ∇W injective on O and range(C) = O′ open (the interior of the simplex Δ(A)). Define the Legendre transform V(y) = y·C⁻¹(y) − W(C⁻¹(y)) on O′. Then V is C² on O′, its gradient field is ∇V = C⁻¹ (hence V is strictly convex on O′), ‖∇V(y)‖ → ∞ as y approaches any boundary point of O′, and for every payoff vector π ∈ O the choice vector C(π) is the unique maximizer of y ↦ (∑ᵢ yᵢπᵢ) − V(y) over O′. This is the Rockafellar (1970) Theorem 26.5 duality package — the exact bridge from the analytic children of Theorem 2.1 of Hofbauer–Sandholm (2002) to its admissible-perturbation conclusion.
-- source:
--   Hofbauer, J. and Sandholm, W. H., 'On the Global Convergence of Stochastic Fictitious Play', Econometrica 70(6), 2002, proof of Theorem 2.1 (pp. 5–7); Rockafellar, R. T., Convex Analysis, 1970, Theorem 26.5. Bridge node #2 in stochfictplay_triage.md ('Named publish-candidate children'), decomposition child of StochFictPlay.DiscreteChoice.exists_admissible_perturbation (Thm 2.1, Mission I: 8d9182ea-3ec4-465c-8532-7dce6b690d44).

import Mathlib

namespace StochFictPlay.DiscreteChoice

/-- Rockafellar (1970) Theorem 26.5 instantiated for the stochastic-fictitious-play
perturbation (Hofbauer--Sandholm 2002, proof of Theorem 2.1, pp. 5--7).
Given a C1 strictly convex potential `W` on the open tangent space `O` (the role of
`R_0^n`), whose gradient field `C = ∇W` is injective on `O` with open range `O'` (the
role of `int Δ(A)`), the Legendre transform
`V y = y · C⁻¹(y) - W (C⁻¹ y)` on `O'` satisfies the full duality package:
`V` is C2 on `O'` with gradient field `∇V = C⁻¹` (hence strictly convex on `O'`),
`‖∇V(y)‖ → ∞` as `y` approaches any boundary point of `O'`, and for every payoff
vector `π ∈ O` the choice vector `C π` is the unique maximizer of
`y ↦ (∑ᵢ yᵢ πᵢ) - V y` over `O'`. -/
theorem legendre_duality_strictlyConvex {n : ℕ} (W : (Fin n → ℝ) → ℝ)
    (O : Set (Fin n → ℝ)) (hO : IsOpen O) (hW : StrictConvexOn ℝ O W)
    (C : (Fin n → ℝ) → (Fin n → ℝ))
    (hgrad : ∀ x ∈ O, ∀ i : Fin n,
      C x i = fderiv ℝ W x ((Pi.single i (1 : ℝ)) : Fin n → ℝ))
    (hinjC : Set.InjOn C O)
    (O' : Set (Fin n → ℝ)) (hO' : IsOpen O') (hrange : C '' O = O')
    (V : (Fin n → ℝ) → ℝ)
    (hV : ∀ y ∈ O', V y =
      Finset.sum Finset.univ (fun i => y i * Function.invFun C y i)
        - W (Function.invFun C y)) :
    (ContDiffOn ℝ 2 V O')
      ∧ (∀ y ∈ O', ∀ i : Fin n,
          fderiv ℝ V y ((Pi.single i (1 : ℝ)) : Fin n → ℝ) = Function.invFun C y i)
      ∧ StrictConvexOn ℝ O' V
      ∧ (∀ y₀ ∈ frontier O', ∀ M : ℝ, ∀ᶠ y in nhdsWithin y₀ O',
          M < ‖((fun i : Fin n => fderiv ℝ V y ((Pi.single i (1 : ℝ)) : Fin n → ℝ)) :
            Fin n → ℝ)‖)
      ∧ ∀ π ∈ O,
          IsMaxOn (fun y => Finset.sum Finset.univ (fun i => y i * π i) - V y) O' (C π)
            ∧ ∀ y ∈ O',
              IsMaxOn (fun y => Finset.sum Finset.univ (fun i => y i * π i) - V y) O' y
                → y = C π := by
  sorry

end StochFictPlay.DiscreteChoice
