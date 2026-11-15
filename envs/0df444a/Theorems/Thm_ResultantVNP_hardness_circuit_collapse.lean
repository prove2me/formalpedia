-- Prove2me | Theorems.Thm_ResultantVNP_hardness_circuit_collapse
-- name    : ResultantVNP.hardness_circuit_collapse
-- status  : Proved
-- author  : @gjindal
-- created : 2026-11-14T10:56:33.289996+00:00
-- url     : https://prove2.me/theorems/a455dfb4-e7b7-4646-bf4d-0ab0cc488959
-- title:
--   Polynomial circuits for a VNP-hard family imply VP = VNP
-- statement:
--   Let $(G_m)$ be a family of polynomials over $\mathbb C$ and let $\ell\ge1$. Suppose the family $(G_m)_{m\ge\ell}$ is VNP-hard under p-projections, and suppose $(G_m)_{m\ge1}$ has polynomial-size arithmetic circuits. Then
--
--   $$\mathrm{VP}=\mathrm{VNP}.$$
--
--   The conclusion does not require polynomial degree or polynomially many variables for $G_m$ itself: each projected target family already belongs to VNP, and therefore has those bounds. This is the complexity-class closure step in the tensor determinant circuit lower-bound argument.
-- source:
--   Auxiliary closure claim for Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission #1103, proof of Theorem 1.4, p.17, and definitions of VP, VNP and p-projections, Section 3.1, p.14. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1103.pdf

import Mathlib
import Definitions.Def_ResultantVNP_IsVNPHardPProj
import Definitions.Def_ResultantVNP_HasPolySizeCircuits

theorem ResultantVNP.hardness_circuit_collapse {τ : ℕ → Type} (G : ∀ m, MvPolynomial (τ m) ℂ) (lo : ℕ)
    (hlo : 1 ≤ lo) (hhard : ResultantVNP.IsVNPHardPProj G lo)
    (hcirc : ResultantVNP.HasPolySizeCircuits G) : ResultantVNP.VP = ResultantVNP.VNP := by sorry
