-- Prove2me | Theorems.Thm_ValuationSubring_existsUnique_isRoot_residue_eq_of_rootMultiplicity_map_residue_eq_one
-- name    : ValuationSubring.existsUnique_isRoot_residue_eq_of_rootMultiplicity_map_residue_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/b9d47966-2289-543c-b1a6-5dffaedafd61
-- title:
--   Unique integral root lifting a simple root of the reduction
-- statement:
--   Let $K$ be a field and $A$ a valuation subring of $K$, with residue field $\kappa = \mathrm{ResidueField}\,A$ and reduction map $\mathrm{residue}_A \colon A \to \kappa$. Let $g \in A[X]$, and assume that the image of $g$ in $K[X]$ under the inclusion $A \hookrightarrow K$ splits, i.e. factors into linear factors over $K$. Let $b \in \kappa$ and assume that the root multiplicity of $b$ in the reduction of $g$, the image of $g$ in $\kappa[X]$ under $\mathrm{residue}_A$, equals $1$. The conclusion is that there exists exactly one element $r \in K$ such that $r$ is a root of $g$ viewed in $K[X]$ and, moreover, $r$ lies in $A$ and the reduction of $r$ (as an element of $A$) is $b$. Uniqueness is asserted among elements of $K$ satisfying this conjunction; the membership $r \in A$ is part of the asserted property rather than a hypothesis on $r$.
--
--   This is the elementary split case of Hensel's lemma for valuation rings: a simple root of the reduction lifts to a unique $A$-integral root of $g$, with no completeness hypothesis on $K$ since splitting over $K$ is assumed. It is used in the analysis of nodes on modular curves, to produce the unique place at which a node coordinate takes a prescribed value.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_existsUnique_isRoot_residue_eq_of_rootMultiplicity_map_residue_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem ValuationSubring.existsUnique_isRoot_residue_eq_of_rootMultiplicity_map_residue_eq_one
    {K : Type*} [Field K] (A : ValuationSubring K) (g : Polynomial A)
    (hsplit : (g.map (algebraMap A K)).Splits)
    (b : IsLocalRing.ResidueField A) (hb : (g.map (IsLocalRing.residue A)).rootMultiplicity b = 1) :
    ∃! r : K, (g.map (algebraMap A K)).IsRoot r ∧ ∃ h : r ∈ A, IsLocalRing.residue A ⟨r, h⟩ = b := by sorry
