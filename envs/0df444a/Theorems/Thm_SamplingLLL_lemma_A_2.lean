-- Prove2me | Theorems.Thm_SamplingLLL_lemma_A_2
-- name    : SamplingLLL.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:53:59.200729+00:00
-- url     : https://prove2.me/theorems/8018896e-b7d0-479e-9b3c-eeba75308ee0
-- title:
--   Lemma A.2, p.19 — exploration identity
-- statement:
--   For every membership exploration with distinguished element $c$ and every set $B$ with $c\in B\subseteq C$,
--   $$
--   \mathbf 1\{B=\{c\}\}=\sum_t(-1)^{|Y_t|-1}\mathbf 1\{Y_t\subseteq B,\ L_t\cap B=\emptyset\}. \tag{1}
--   $$
--   Equivalently, for arbitrary commuting variables $(z_d)_{d\in C}$,
--   $$
--   z_c\prod_{d\ne c}(1-z_d)=\sum_t(-1)^{|Y_t|-1}\prod_{d\in Y_t}z_d\prod_{d\in L_t}(1-z_d).
--   $$
--   This is the signed inclusion–exclusion on which the packet identity rests.
--
--   Differences from the source:
--   - encoding: a finite constraint set and a decision tree → constraints indexed by a `Fin m`, the tree as a next-query rule on pairs (Y, N); reason: every finite set relabels to `Fin m`, and a node of a tree is determined by (Y, N); no instance changes
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Lemma A.2, eq. (1), p.19

import Mathlib
import Definitions.Def_SamplingLLL_Exploration

set_option autoImplicit false

namespace SamplingLLL

/-- Lemma A.2 (Exploration identity), p.19, identity (1) and its polynomial form, for every
membership exploration on a finite constraint set.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Lemma A.2, eq. (1), p.19. -/
theorem lemma_A_2 {m : ℕ} (C : Finset (Fin m)) (c : Fin m) (hc : c ∈ C) (next : NextQuery m)
    (hnext : IsExploration C c next) :
    (∀ B : Finset (Fin m), c ∈ B → B ⊆ C →
      (if B = {c} then (1 : ℤ) else 0) =
        ∑ t ∈ leaves C c next, sign t * (if Active C t B then 1 else 0)) ∧
    (∀ (R : Type) [CommRing R] (z : Fin m → R),
      z c * ∏ d ∈ C.erase c, (1 - z d) =
        ∑ t ∈ leaves C c next,
          (sign t : R) * ((∏ d ∈ t.1, z d) * ∏ d ∈ unqueried C t, (1 - z d))) := by sorry

end SamplingLLL
