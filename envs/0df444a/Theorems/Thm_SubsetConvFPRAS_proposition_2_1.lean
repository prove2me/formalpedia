-- Prove2me | Theorems.Thm_SubsetConvFPRAS_proposition_2_1
-- name    : SubsetConvFPRAS.proposition_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:19:34.453018+00:00
-- url     : https://prove2.me/theorems/01d237dc-2910-44f0-adbe-65400ed43caa
-- title:
--   Proposition 2.1 — two variational formulas for the spectral gap
-- statement:
--   Let $\pi$ be a positive probability law on a finite set $\Omega$ and $r$ the rates of an irreducible chain reversible with respect to $\pi$, with Laplacian $L=L_r$. Then
--   $$\inf_{f\ \text{nonconstant}}\frac{\langle f,Lf\rangle_\pi}{\operatorname{Var}_\pi[f]}=\inf_{f\ \text{nonconstant}}\frac{\langle Lf,Lf\rangle_\pi}{\langle f,Lf\rangle_\pi}.$$
--
--   This is the abstract criterion of the integrated Bochner method: to bound the spectral gap below by $\gamma$ it suffices to show $\langle Lf,Lf\rangle_\pi\ge\gamma\langle f,Lf\rangle_\pi$.
--
--   Differences from the source:
--   - encoding: inf over nonconstant f → sInf of the set of ratios over nonconstant f; reason: on a one-point Ω both sets are empty and Lean's sInf ∅ = 0 gives the same value on both sides; otherwise the ratios are well defined since ⟨f,Lf⟩ > 0 for nonconstant f under irreducibility
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Proposition 2.1, p.11 (proof p.17)

import Mathlib
import Definitions.Def_SubsetConvFPRAS_ReversibleChain

open scoped Classical

namespace SubsetConvFPRAS

/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Proposition 2.1, p.11. For an irreducible reversible
chain, the two infima over nonconstant `f` agree.

**Formalization Note.** On a one-state space both sets are empty and `sInf ∅ = 0` on both sides. -/
theorem proposition_2_1 {Ω : Type} [Fintype Ω] (π : Ω → ℝ) (r : Ω → Ω → ℝ)
    (hr : IsReversibleChain π r) (hi : IsIrreducible r) :
    sInf (gapRatiosVar π r) = sInf (gapRatiosSq π r) := by sorry

end SubsetConvFPRAS
