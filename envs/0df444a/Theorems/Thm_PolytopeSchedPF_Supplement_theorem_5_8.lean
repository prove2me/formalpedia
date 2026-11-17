-- Prove2me | Theorems.Thm_PolytopeSchedPF_Supplement_theorem_5_8
-- name    : PolytopeSchedPF.Supplement.theorem_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:23:17.19598+00:00
-- url     : https://prove2.me/theorems/0cee291c-a9e3-4152-a473-019ca5fa49a9
-- title:
--   Theorem 5.8 — if $\mathrm{OPT}$ is concave for every weight vector, then the rate polytope is support submodular
-- statement:
--   Let $P\subseteq\mathbb R^n_{\ge0}$ be a downward-closed rate polytope such that, for every weight vector $w\in\mathbb R^n_{>0}$, the optimal-value function
--
--   $$p\longmapsto\mathrm{OPT}(p)$$
--
--   of the instance with rate polytope $P$, weights $w$ and all release dates $0$ is concave on $\mathbb R^n_{\ge0}$. Then $P$ is support submodular: for every $\alpha\in\mathbb R^n_{\ge0}$ the set function $U\mapsto H_\alpha(U)$ is submodular.
--
--   Together with Theorem 5.6 this gives the characterization of Theorem 1.2: support submodularity is exactly concavity of $\mathrm{OPT}$ for all weights.
--
--   Differences from the source:
--   - encoding: a downward-closed (rate) polytope P ⊆ ℝⁿ≥0 → a base RatePolytope {y ≥ 0 | By ≤ 1} with B ≥ 0 and no zero column; reason: base reading R1: every downward-closed polytope containing a positive multiple of each unit vector has such a description
--   - encoding: OPT(p) of the PSP instance with rate polytope P and weights w → the base opt0 P w p (all release dates 0); reason: §5 works with release dates 0; Theorem 1.2 states the same with uniform release dates
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, Theorem 5.8, §5.4, p.30 (PDF p.32); Theorem 1.2, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_PolytopeSchedPF_Orders
import Definitions.Def_PolytopeSchedPF_IsSupportSubmodular

namespace PolytopeSchedPF

namespace Supplement

/-- **Theorem 5.8** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §5.4, p.30). Let
`P ⊆ ℝⁿ_{≥0}` be a downward-closed rate polytope such that, for every weight vector `w ∈ ℝⁿ_{>0}`,
the optimal-value function `p ↦ OPT(p)` of the PSP instance with rate polytope `P` and weights `w` is
concave on `ℝⁿ_{≥0}`. Then `P` is support submodular.

**Formalization Note** `P` is a base `RatePolytope` (reading R1); `OPT` is the base `opt0`
(release dates `0`, as in §5). This is the converse of the published Theorem 5.6. -/
theorem theorem_5_8 {n D : ℕ} (P : RatePolytope n D)
    (hconc : ∀ w : Fin n → ℝ, (∀ j, 0 < w j) →
      ConcaveOn ℝ {p : Fin n → ℝ | ∀ j, 0 ≤ p j} (opt0 P w)) :
    IsSupportSubmodular P := by sorry

end Supplement

end PolytopeSchedPF
