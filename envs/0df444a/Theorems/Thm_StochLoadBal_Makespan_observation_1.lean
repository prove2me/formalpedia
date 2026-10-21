-- Prove2me | Theorems.Thm_StochLoadBal_Makespan_observation_1
-- name    : StochLoadBal.Makespan.observation_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:08.24847+00:00
-- url     : https://prove2.me/theorems/1bc784aa-db63-483e-934c-23be5df0cc62
-- title:
--   Observation 1 — the class loop classifies every machine within m iterations, and at most ℓ machines have class at most ℓ
-- statement:
--   Let $m\ge1$ and let $y$ be a feasible solution of the LP (5)–(9) with parameter $b$. Run the class loop of §3.2 on $y$. Then
--
--   1. the loop terminates within $m$ iterations, so every machine $i$ receives a class $\ell_i$ with $1\le \ell_i\le m$;
--   2. for every $\ell$,
--   $$\#\{i\in[m]:\ \ell_i\le \ell\}\ \le\ \ell .$$
--
--   The second part is the counting fact behind the union bound of Lemma 7: few machines have a small class, and machines of a large class $\ell$ have a tail probability $\ell^{-\alpha}$.
--
--   **Formalization Note** "Terminates in at most $m$ iterations" is stated as: the loop, run with fuel $m$, leaves no machine with the junk class $0$. The second part is stated for every natural number $\ell$; it says nothing new for $\ell>m$ and, for $\ell=0$, repeats that every machine is classified.
-- source:
--   Gupta, Kumar, Nagarajan & Shen, Stochastic Load Balancing on Unrelated Machines, arXiv:1904.07271v1, p. 11, Observation 1

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Rounding

namespace StochLoadBal.Makespan

open MeasureTheory ProbabilityTheory

/-- Observation 1 (p. 11): for a feasible LP solution `y`, the class loop classifies every
machine within its `m` iterations (every class lies in `1, …, m`), and for every `ℓ` at most
`ℓ` machines have class at most `ℓ`. -/
theorem observation_1 {m n : ℕ} (hm : 1 ≤ m) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Fin m → Fin n → Ω → ℝ) (b : ℝ) (y : Fin m → Fin n → ℝ)
    (hy : LPFeasible P X b y) :
    (∀ i, 1 ≤ machineClass P X b y i ∧ machineClass P X b y i ≤ m) ∧
    ∀ ℓ : ℕ, (Finset.univ.filter (fun i => machineClass P X b y i ≤ ℓ)).card ≤ ℓ := by sorry

end StochLoadBal.Makespan
