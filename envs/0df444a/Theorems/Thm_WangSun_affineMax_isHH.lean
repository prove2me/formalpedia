-- Prove2me | Theorems.Thm_WangSun_affineMax_isHH
-- name    : WangSun.affineMax_isHH
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-16T05:20:07.6279+00:00
-- url     : https://prove2.me/theorems/6d8a8c64-9631-49e2-bc37-1b67cbb1f0bc
-- title:
--   Finite affine maxima reduce to $(n+1)$-argument hinges
-- statement:
--   Let $I$ be a nonempty finite index set and let $(\ell_i)_{i\in I}$ be affine functions from $\mathbb{R}^n$ to $\mathbb{R}$. Then the convex piecewise-linear function
--
--   $$
--   x\longmapsto \max_{i\in I}\ell_i(x)
--   $$
--
--   is a finite sum of signed maxima of exactly $n+1$ affine functions. Equivalently, it has a generalized hinging-hyperplane representation of order $n$. Maxima involving fewer than $n+1$ distinct affine functions are represented by repeating arguments, and arbitrary integer coefficients are represented by repeating signed hinge summands.
--
--   This is the single-maximum height-reduction core of the theorem that every piecewise-linear function on $\mathbb{R}^n$ is an integral linear combination of maxima of at most $n+1$ affine functions. It is reusable independently of the lattice-normal-form step for general CPWL functions.
--
--   **Formalization Note** The family is indexed by an arbitrary nonempty finite type. The conclusion uses the shared mission predicate `IsHH` from `Definitions.Def_CPWL`.
-- source:
--   C. Koutschan, B. Moser, A. Ponomarchuk, J. Schicho, Representing Piecewise Linear Functions by Functions with Small Arity, RICAM Report 2023-07, https://www.ricam.oeaw.ac.at/files/reports/23/rep23-07.pdf, Section 2 pp. 3–5, Lemmas 1–3 and Theorem 1 (reduction of a finite affine maximum to an integral linear combination of maxima of at most n+1 affine functions); original result: S. Wang and X. Sun, Generalization of hinging hyperplanes, IEEE TIT 51(12), 2005, Theorem 1.

import Definitions.Def_CPWL

open Finset

namespace WangSun

theorem affineMax_isHH {n : ℕ} {I : Type} [Fintype I] [Nonempty I]
    (L : I → ((Fin n → ℝ) →ᵃ[ℝ] ℝ)) :
    IsHH (fun x => (Finset.univ : Finset I).sup' Finset.univ_nonempty fun i => L i x) := by
  sorry

end WangSun
