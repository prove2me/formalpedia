-- Prove2me | Theorems.Thm_WLight_isBoundedAtImInfty_iff_qExpansion_coeff_lt
-- name    : WLight.isBoundedAtImInfty_iff_qExpansion_coeff_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/be815d01-556d-5c27-880a-6ec1bb314875
-- title:
--   Boundedness at i∞ via vanishing of low q-expansion coefficients
-- statement:
--   Let $N$ be a nonzero natural number, $F\colon \mathfrak H \to \mathbb C$ a function on the upper half-plane, and $M$ a natural number. Assume: $F$ is holomorphic, in the sense of being `MDifferentiable` for the model with corners $\mathcal I(\mathbb C)$ on source and target; the extension $F \circ$ `UpperHalfPlane.ofComplex` of $F$ to $\mathbb C$ is periodic with period $N$; and the pointwise product $F \cdot \Delta^{M}$, where $\Delta$ is `ModularForm.discriminant`, the normalised discriminant cusp form of weight $12$ on $\mathrm{SL}_2(\mathbb Z)$, is bounded along the filter `atImInfty` (i.e. as $\operatorname{Im}\tau \to \infty$). The conclusion is an equivalence: $F$ itself is bounded at $i\infty$ if and only if, for every $n < N\cdot M$, the $n$-th coefficient of the width-$N$ $q$-expansion `UpperHalfPlane.qExpansion N` of $F \cdot \Delta^{M}$ vanishes, that is, the power series of $F\cdot\Delta^{M}$ in $q_N = e^{2\pi i \tau/N}$ begins in degree at least $N M$.
--
--   This is the criterion, in terms of orders of vanishing at the cusp $i\infty$, for a periodic holomorphic function to be bounded there: since $\Delta^{M}$ has $q_N$-order exactly $NM$, boundedness of $F$ is exactly the statement that multiplication by $\Delta^{M}$ produces no coefficients below degree $NM$. It is the boundedness companion of the corresponding vanishing criterion, and is used in the proof of [`ModularForm.exists_gamma1_frickeRational_sigmaTransport`](thm.html#ModularForm.exists_gamma1_frickeRational_sigmaTransport) to transport growth conditions at the cusps along Galois twists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WLight_isBoundedAtImInfty_iff_qExpansion_coeff_lt.lean

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Geometry.Manifold.Notation
import Mathlib.FieldTheory.IntermediateField.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem WLight.isBoundedAtImInfty_iff_qExpansion_coeff_lt (N : ℕ) [NeZero N] {F : ℍ → ℂ} {M : ℕ}
    (hFhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hFper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) N)
    (hFbd : IsBoundedAtImInfty (F * ModularForm.discriminant ^ M)) :
    IsBoundedAtImInfty F ↔
      ∀ n < N * M,
        (UpperHalfPlane.qExpansion N (F * ModularForm.discriminant ^ M)).coeff n = 0 := by sorry
