-- Prove2me | Theorems.Thm_ToricFoliations_projective_space_bundle
-- name    : ToricFoliations.projective_space_bundle
-- status  : Open
-- author  : @hiraeth
-- created : 2026-10-07T12:33:19.096124+00:00
-- url     : https://prove2.me/theorems/9d708ac0-9e11-4e84-9b9a-810a6bd175d7
-- title:
--   Theorem 1.3(2) — long extremal rays give a $\mathbb P^r$-bundle and $l_{\mathscr F}(R)=r+1$
-- statement:
--   **theorem_title:** Theorem 1.3(2) — long extremal rays give a $\mathbb P^r$-bundle and $l_{\mathscr F}(R)=r+1$
--
--   Let $X$ be a projective $\mathbb Q$-factorial toric variety and let
--   $\mathscr F$ be a toric foliation of rank $r$ on $X$, represented by
--   $V\subseteq N_{\mathbb C}$. Let $R$ be an extremal ray of
--   $\mathrm{NE}(X)$. If
--
--   $$
--   l_{\mathscr F}(R)>r,
--   $$
--
--   then the extremal contraction $\varphi_R:X\to Y$ associated to $R$ is a
--   $\mathbb P^r$-bundle over $Y$, the foliation is the relative tangent sheaf
--   $\mathscr F=\mathscr T_{X/Y}$ of $\varphi_R$, and in particular
--   $\mathscr F$ is locally free and $l_{\mathscr F}(R)=r+1$.
--
--   In the combinatorial core formalized here, the $\mathbb P^r$-bundle
--   conclusion is the statement that the tail vectors $v_{n-r+1},\dots,v_{n+1}$
--   satisfy $v_{n-r+1}+\cdots+v_{n+1}=0$, span a saturated rank-$r$ sublattice of
--   $N$, and give a lattice splitting
--   $N\cong\mathbb Z^r\times\mathbb Z^{n-r}$ (`IsProjectiveSpaceBundle`), and that
--   the length on every curve of the ray equals $r+1$.
--
--   **Formalization Note.** The sheaf-theoretic wrapper (contracting morphisms,
--   relative tangent sheaf) is not yet in Mathlib; `ExtremalRay.isExtremal` marks
--   the boundary where the toric Mori theory attaches. Nothing in the statement is
--   vacuous: `WallData` carries real content and `hlong` is the nontrivial
--   hypothesis of the theorem.
-- source:
--   Fujino--Sato 2024, A remark on toric foliations, Arch. Math. 122 (2024) 621--627, https://doi.org/10.1007/s00013-024-01991-1 (arXiv:2309.09461), Section 1, Theorem 1.3(2)

import Mathlib
import Definitions.Def_ToricFoliations

open scoped BigOperators

namespace ToricFoliations

/--
Theorem 1.3(2) of the paper (main theorem): if the length of an extremal ray
`R` satisfies `l_F(R) > r`, then the associated extremal contraction is a
`P^r`-bundle, the foliation is the relative tangent sheaf of that contraction,
and in particular `l_F(R) = r + 1`.

In this combinatorial core the `P^r`-bundle conclusion is encoded by the
lattice splitting and tail-vector span of `IsProjectiveSpaceBundle`.
-/
theorem projective_space_bundle {n r : ℕ} (hr : r ≤ n) (R : ExtremalRay n)
    (hExt : R.isExtremal) (C : WallData n) (hC : C ∈ R.curves)
    (V : Submodule ℂ (Complexified n))
    (hrank : Module.finrank ℂ V = r)
    (hlong : r < rayLength R V) :
    IsProjectiveSpaceBundle hr C ∧ curveLength C V = r + 1 := by
  sorry

end ToricFoliations
