-- Prove2me | Theorems.Thm_PriorityAlloc_DAFlex_daop_monotone_cutoff_exists
-- name    : PriorityAlloc.DAFlex.daop_monotone_cutoff_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:08.026265+00:00
-- url     : https://prove2.me/theorems/ebaf4c67-172c-4de2-bac8-67c63081f985
-- title:
--   App. A.2, p. 34 — the DA operator is a monotone self-map of [0,B]^n, so the DA cutoff (least fixed point) exists
-- statement:
--   Let $M$ satisfy the standing assumptions, let $G_t$ be probability distributions of priorities, $q \in \mathbb{R}^n$ quotas and $B > 0$. Then the DA operator $DA$ of Algorithm 2 on $\Pi = [0,B]^n$
--
--   1. maps $[0,B]^n$ into itself;
--   2. is monotone on $[0,B]^n$: $z \le z'$ implies $DA(z) \le DA(z')$;
--   3. has a minimum fixed point in $[0,B]^n$, i.e. the DA cutoff $z^{DA(M,G,q)}$ exists.
--
--   This is the well-posedness statement behind the definition of the DA cutoff: the set of fixed points is a non-empty lattice by Knaster–Tarski, and its least element defines the DA mechanism.
--
--   **Formalization Note** The operator is the clamped one of the definitions file; the existence claim is stated as `∃ z, IsDACutoff M G q B z`.
-- source:
--   Shi, Optimal Priority-Based Allocation Mechanisms, SSRN manuscript 3425348 (June 2020; published Management Science 2022, doi:10.1287/mnsc.2020.3925), p. 34, App. A.2, paragraph after Algorithm 2

import Mathlib
import Definitions.Def_PriorityAlloc_DAFlex_Model

namespace PriorityAlloc.DAFlex

open MeasureTheory Classical

variable {m n : ℕ}

/-- App. A.2, p. 34: the DA operator maps `Π = [0,B]^n` to itself and is monotone there, so by
Knaster–Tarski its fixed points in `[0,B]^n` have a minimum element `z^{DA(M,G,q)}`. -/
theorem daop_monotone_cutoff_exists (M : Market m n) (hM : M.Standing)
    (G : Fin m → Measure (Fin n → ℝ)) (hG : ∀ t, IsProbabilityMeasure (G t))
    (q : Fin n → ℝ) (B : ℝ) (hB : 0 < B) :
    (∀ z ∈ box B, DAop M G q B z ∈ box B) ∧
      (∀ z ∈ box B, ∀ z' ∈ box B, z ≤ z' → DAop M G q B z ≤ DAop M G q B z') ∧
      ∃ z, IsDACutoff M G q B z := by sorry

end PriorityAlloc.DAFlex
