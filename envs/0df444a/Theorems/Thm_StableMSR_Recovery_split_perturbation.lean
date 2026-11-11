-- Prove2me | Theorems.Thm_StableMSR_Recovery_split_perturbation
-- name    : StableMSR.Recovery.split_perturbation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:32.410401+00:00
-- url     : https://prove2.me/theorems/e3257e5c-888d-475f-9da9-311ebe79dd26
-- title:
--   Lemma 3.5 — split perturbation
-- statement:
--   Let $C$ be any nonsingleton subset of a finite real metric, with radius $r=r_d(C)$, and let $\gamma>1$. There are an optimal center $c\in C$, a point $p\in C\setminus\{c\}$, and one symmetric $\gamma$-perturbation $d'$ that changes only internal pairs of $C$, such that
--   $$
--   r_{d'}(C)=\gamma r,\qquad r_{d'}(C\setminus\{p\})\le r.
--   $$
--   The perturbation need not be a metric. Both radius statements use the same perturbation. This is the local construction used in the merge-and-split inequality.
--
--   Differences from the source:
--   - encoding: An arbitrary finite real metric space with fixed input order and unordered clusters → Points are Fin n; clusters and unordered partitions are finite sets; metric arrays are Mathlib metric distances; reason: Relabelling preserves every finite ordered instance, all distance values, and every unordered partition
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), Lemma 3.5, p. 5; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Geometry

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

theorem split_perturbation {n : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) (γ : ℝ) (hγ : 1 < γ)
    (C : Cluster n) (hC : 2 ≤ C.card) :
    ∃ c p : Point n, OptimalCenter d C c ∧ p ∈ C ∧ p ≠ c ∧
      ∃ d' : Point n → Point n → ℝ, Perturbation d γ d' ∧
        (∀ x y, ¬ (x ∈ C ∧ y ∈ C) → d' x y = d x y) ∧
        radius d' C = γ * radius d C ∧ radius d' (C.erase p) ≤ radius d C := by sorry

end StableMSR.Recovery
