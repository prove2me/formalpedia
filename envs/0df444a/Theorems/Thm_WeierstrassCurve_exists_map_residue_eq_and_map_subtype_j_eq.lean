-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_map_residue_eq_and_map_subtype_j_eq
-- name    : WeierstrassCurve.exists_map_residue_eq_and_map_subtype_j_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/e7b0ef0d-6dc5-575e-bc21-22d20c133d67
-- title:
--   Lifting a Weierstrass model with prescribed reduction and j
-- statement:
--   Let $L$ be an algebraically closed field and let $A$ be a valuation subring of $L$, a local ring with residue field $\kappa_A$ and residue map $\mathrm{res} : A \to \kappa_A$. Let $W$ be a Weierstrass curve over $\kappa_A$, given by coefficients $a_1,a_2,a_3,a_4,a_6 \in \kappa_A$, which is elliptic in the sense that its discriminant $\Delta(W)$ is a unit of $\kappa_A$, so that its $j$-invariant $j(W)$ is defined. Let $\beta \in A$ be an element whose residue class is $j(W)$, i.e. $\mathrm{res}(\beta) = j(W)$. The assertion is that there exist a Weierstrass curve $E$ over $A$ and a witness that the base change $E \otimes_A L$ of $E$ along the inclusion $A \hookrightarrow L$ is elliptic, i.e. that $\Delta(E)$ is a unit in $L$ (equivalently nonzero), such that the coefficientwise reduction of $E$ along $\mathrm{res}$ equals $W$ exactly, coefficient by coefficient, and the $j$-invariant of $E \otimes_A L$, which is defined by the witness just mentioned, equals the image of $\beta$ in $L$. No hypothesis is imposed on the residue characteristic or on the value of $j(W)$.
--
--   This is the lifting step producing from an elliptic curve over the residue field of a valuation subring an integral Weierstrass model with good reduction whose special fibre is the given curve and whose generic $j$-invariant is a prescribed lift of $j(W)$, valid in all residue characteristics and for all $j$, including $j \in \{0,1728\}$ in residue characteristic $2$ or $3$. It is used in the construction of curves over $L$ with prescribed reduction behaviour, feeding the results on variable changes compatible with reduction maps on rational points for algebraic $j$ and in characteristic $2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_map_residue_eq_and_map_subtype_j_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_map_residue_eq_and_map_subtype_j_eq {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) (W : WeierstrassCurve (IsLocalRing.ResidueField A)) [W.IsElliptic] (β : A) (hres : IsLocalRing.residue A β = W.j) : ∃ (E : WeierstrassCurve A) (_ : (E.map A.subtype).IsElliptic), E.map (IsLocalRing.residue A) = W ∧ (E.map A.subtype).j = (β : L) := by sorry
