-- Prove2me | Theorems.Thm_SolomonRWRE_DiffEq_proof_4_4_limsup
-- name    : SolomonRWRE.DiffEq.proof_4_4_limsup
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:07.320413+00:00
-- url     : https://prove2.me/theorems/d7dcb9d4-646d-4519-8b9a-3360e9151791
-- title:
--   Proof of Theorem (4.4), p. 29 — if ν < 1, lim sup (1/n) Σ_{k=1}^n Z_k ≤ ν/(1 − ν) a.e.
-- statement:
--   Let $\sigma_1,\sigma_2,\dots$ be i.i.d. nonnegative random variables with mean $\nu=E(\sigma)<1$ and let $Z_n$ solve (4.1). Then almost surely
--   $$
--   \limsup_{n\to\infty}\frac1n\sum_{k=1}^{n}Z_k\ \le\ \frac{\nu}{1-\nu}.
--   $$
--
--   Together with the lower bound $\liminf\ge\sum_{k\ge1}\nu^k=\nu/(1-\nu)$ this gives the first case of Theorem (4.4).
--
--   **Formalization Note** The averages are mapped to $[0,\infty]$, which loses nothing since $Z_k\ge0$; under $\nu<1$, $\nu/(1-\nu)$ is a finite nonnegative number.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 29, proof of Theorem (4.4), from "Let ν < 1; it suffices to show" to the end of the proof

import Mathlib
import Definitions.Def_SolomonRWRE_DiffEq_System

open MeasureTheory ProbabilityTheory Filter Topology

namespace SolomonRWRE.DiffEq

/-- **Proof of Theorem (4.4), p. 29** (unnumbered): "Let `ν < 1`; it suffices to show
`lim sup_{n→∞} (1/n) Σ_{k=1}^n Z_k ≤ ν/(1 − ν)` a.e." — the claim the rest of the proof
establishes with Birkhoff's ergodic theorem.

**Formalization Note.** In `[0, ∞]`; under `ν < 1`, `ν` is finite and `1 − ν > 0`, so
`ν / (1 − ν)` is the real number `ν/(1 − ν)`. -/
theorem proof_4_4_limsup {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℕ → Ω → ℝ) (hσ : IsIIDNonneg P σ) (hν : nu P σ < 1) :
    ∀ᵐ ω ∂P, limsup (fun n : ℕ => ENNReal.ofReal ((∑ k ∈ Finset.Icc 1 n, Z σ k ω) / n))
      atTop ≤ nu P σ / (1 - nu P σ) := by sorry

end SolomonRWRE.DiffEq
