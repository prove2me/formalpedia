-- Prove2me | Theorems.Thm_WeldedPath_compressed_assertion_projection_bound
-- name    : WeldedPath.compressed_assertion_projection_bound
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-18T17:47:44.004451+00:00
-- url     : https://prove2.me/theorems/dbdc32c7-fa78-489a-8dee-92f57c19e2aa
-- title:
--   Compressed assertions remain close to the canonical completion spaces
-- statement:
--   Let $s,r$ be nonnegative integers with $3r+2\le s$, and fix a query input $x\in[s]$. Let $L_j$ project onto databases of size $j$, and let $K_j=\operatorname{ran}(\Gamma_j^\dagger)$ be the canonical completion space. For each response $y\in[s]$, define the compressed assertion and its component outside $K_j$ by
--
--   $$A_y=pC_x\,\mathbf1_{I(x)=y}\,pC_x,\qquad Z_{j,y}=(I-\Pi_{K_j})L_j A_y.$$
--
--   For every $a\in K_r$,
--
--   $$\sum_y\left(\|Z_{r+1,y}a\|^2+\|Z_{r,y}a\|^2\right)\le\frac{204}{s-r}\|a\|^2.$$
--
--   For every family $(a_y)_y$ with $a_y\in K_r$,
--
--   $$\left\|\sum_y Z_{r+1,y}a_y\right\|^2+\left\|\sum_y Z_{r,y}a_y\right\|^2\le\frac{204}{s-r}\sum_y\|a_y\|^2.$$
--
--   These column and row estimates control the part of a compressed assertion that leaves the canonical completion spaces. The degree-zero case is included. All operators are the canonical database operators; comparison of the components within the completion spaces is a separate estimate.
-- source:
--   Carolan and Majenz, Compressed Permutation Oracles Revisited, https://arxiv.org/html/2609.28469v1, Lemma 4.13 and the deduction of equation (23), with a relaxed absolute constant. Canonical WeldedPath compression and completion operators are from https://arxiv.org/html/2611.05912v1. This result concerns the component outside the completion range; it does not assert the full exact-versus-compressed query comparison.

import Mathlib
import Definitions.Def_WeldedPath_exactCpO

set_option autoImplicit false
open Classical
open scoped BigOperators

namespace WeldedPath

theorem compressed_assertion_projection_bound (s r : ℕ) (hsmall : 3*r+2 ≤ s) (x : Fin s) :
    let K := fun j : ℕ => (ContinuousLinearMap.adjoint (Gam s j)).range
    let L := fun j : ℕ => diagProj (fun I : InjDb s => I.size=j)
    let A := fun y : Fin s => (pC s x).comp
      ((diagProj (fun I : InjDb s => I x=some y)).comp (pC s x))
    (∀ a : Hil (InjDb s), a∈K r →
      (∑ y : Fin s,
        (‖L (r+1) (A y a)-(K (r+1)).starProjection (L (r+1) (A y a))‖^2+
          ‖L r (A y a)-(K r).starProjection (L r (A y a))‖^2)) ≤
        204*((s-r : ℕ) : ℝ)⁻¹*‖a‖^2) ∧
    (∀ a : Fin s → Hil (InjDb s), (∀ y,a y∈K r) →
      ‖(∑ y : Fin s,L (r+1) (A y (a y)))-
        (K (r+1)).starProjection (∑ y : Fin s,L (r+1) (A y (a y)))‖^2+
        ‖(∑ y : Fin s,L r (A y (a y)))-
          (K r).starProjection (∑ y : Fin s,L r (A y (a y)))‖^2 ≤
        204*((s-r : ℕ) : ℝ)⁻¹*(∑ y : Fin s,‖a y‖^2)) := by
  sorry

end WeldedPath
