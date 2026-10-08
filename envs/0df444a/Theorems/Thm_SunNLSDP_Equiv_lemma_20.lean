-- Prove2me | Theorems.Thm_SunNLSDP_Equiv_lemma_20
-- name    : SunNLSDP.Equiv.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:45.897988+00:00
-- url     : https://prove2.me/theorems/465c848d-116f-4929-95c5-472c4cc948b5
-- title:
--   Lemma 20, p. 22 — ∂_BΦ(0) = ∂_BF(x̄, ζ̄, Γ̄) for Φ = F′(x̄, ζ̄, Γ̄; ·)
-- statement:
--   Let $(\bar x,\bar\zeta,\bar\Gamma)$ be a KKT point of (NLSDP), $F$ the KKT map (51), and $\Phi(\delta):=F'(\bar x,\bar\zeta,\bar\Gamma;\delta)$ its directional derivative (67). Then
--
--   $$\partial_B\Phi(0)=\partial_BF(\bar x,\bar\zeta,\bar\Gamma).$$
--
--   The lemma lets every statement about the B-subdifferential of the nonsmooth KKT map be read off the piecewise-linear map $\Phi$, which gives the equivalence of (b) and (j) in Theorem 21.
--
--   **Formalization Note.** $\Phi$ is defined as the one-sided directional derivative of $F$ at the KKT point (the left side of (67)); its existence is part of what the paper establishes, not an assumption.
-- source:
--   Sun, The strong second order sufficient condition and constraint nondegeneracy in nonlinear semidefinite programming and their implications, preprint dated May 15, 2005, p. 22, Lemma 20 ((67))

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_SunNLSDP_Equiv_Setting

open scoped RealInnerProductSpace Topology
open Filter NonsmoothNewton.Shared NonsmoothNewton.Local

namespace SunNLSDP.Equiv
theorem lemma_20 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] {m : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    (P : NLSDP X m n) (xbar : X) (ζbar : EuclideanSpace ℝ (Fin m)) (Γbar : SymMat n)
    (hfeas : P.feasible xbar) (hKKT : (ζbar, Γbar) ∈ P.multipliers xbar) :
    bJac (kktDirDeriv P (kktPt xbar ζbar Γbar)) 0 = bJac (kktMap P) (kktPt xbar ζbar Γbar) := by sorry
end SunNLSDP.Equiv
