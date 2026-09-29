-- Prove2me | Theorems.Thm_WeierstrassCurve_natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed
-- name    : WeierstrassCurve.natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/94a534c6-fb29-5f54-a382-f8be7c08c792
-- title:
--   Cyclic subgroups of order n number ψ(n)
-- statement:
--   Let $F$ and $K$ be fields with $K$ an $F$-algebra and $K$ algebraically closed, let $W$ be a Weierstrass curve over $F$ which is elliptic (`W.IsElliptic`), and let $n$ be a natural number whose image in $K$ is nonzero, so in particular $n \ge 1$ and $n$ is invertible in $K$ when $K$ has positive characteristic. Write $(W⁄K)$ for the base change of $W$ to $K$ and $(W⁄K).\mathrm{Point}$ for the additive group of points of the associated affine curve over $K$. The assertion is an equality of natural numbers: the cardinality of the type of subgroups $G$ of $(W⁄K).\mathrm{Point}$ satisfying both that $G$ is an additively cyclic group and that $\mathrm{Nat.card}\,G = n$ equals $\mathrm{ModularCurve.dedekindPsi}\,n$, which by definition is the sum $\sum_{d \mid n,\ d \text{ squarefree}} n/d$ over the squarefree divisors of $n$, i.e. the Dedekind value $\psi(n) = n\prod_{p \mid n}(1 + 1/p)$. No condition confining $G$ to the $n$-torsion is imposed: the subgroups are counted among all subgroups of the full group of points.
--
--   This is the moduli-theoretic count underlying $\Gamma_0(n)$-level structures: an elliptic curve over an algebraically closed field of characteristic not dividing $n$ carries exactly $\psi(n) = [\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(n)]$ cyclic subgroups of order $n$, equivalently $\psi(n)$ cyclic $n$-isogenies. It is used in the analysis of the modular polynomial of level $n$, in particular in the results identifying the roots of its specialisation at a $j$-invariant and in the separability statements for such specialisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed
    {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    Nat.card {G : AddSubgroup (W⁄K).Point // IsAddCyclic G ∧ Nat.card G = n}
      = ModularCurve.dedekindPsi n := by sorry
