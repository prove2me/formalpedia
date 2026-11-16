-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_Supplement_theorem_6_1
-- name    : QuantumSymmetryBreaking.CycleColoring.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:06:32.782962+00:00
-- url     : https://prove2.me/theorems/16e32f06-7820-46ec-8972-b1d83ae6cb26
-- title:
--   Theorem 6.1 — Known-size directed-cycle coloring with global high probability
-- statement:
--   For every real C≥1 there is one family of anonymous one-way one-round algorithms, using exactly 20000 colors, indexed by the known size bound n. Every family member consists of a finite bipartite density matrix and a 20000-outcome POVM. For every directed cycle of actual size 3≤m≤n, its full Born-rule output satisfies
--
--   $$\Pr[\text{all edges are properly colored}]\ge 1-n^{-C}.$$
--
--   The density matrix, measurement and register sizes are chosen from n before the actual cycle size m. Private computation is unrestricted. This is the global-success companion to the per-edge goal, with the known bound allowed to control local resources.
--
--   Differences from the source:
--   - encoding: known network size upper bound n and actual cycle size → separate n and m, with 3 ≤ m ≤ n and NeZero m; reason: §3 defines n as an upper bound; NeZero enables ZMod indexing
--   - encoding: one-round one-way quantum algorithm → family of finite mixed states and POVMs using the published properColoringProb; reason: the source’s anonymous construction implements this operational specialization; Fin 20000 is the exact palette
-- source:
--   Maxime Flin, Longcheng Li, Jukka Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), Theorem 6.1, p.28 (PDF 31)

import Mathlib
import Definitions.Def_QuantumCycleColoring_FourColor_CycleAlgorithm
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_FiniteRealization

set_option autoImplicit false
open scoped ComplexOrder

namespace QuantumSymmetryBreaking.CycleColoring.Supplement

open QuantumCycleColoring.FourColor

/-- Theorem 6.1, printed p.28 (PDF 31): one-way one-round global success
with known size upper bound n. The family is fixed before the actual cycle size m. -/
theorem theorem_6_1 (C : ℝ) (hC : 1 ≤ C) :
    ∃ D N : ℕ → ℕ, (∀ n, 0 < D n ∧ 0 < N n) ∧
    ∃ ρ : (n : ℕ) → Matrix (Fin (D n) × Fin (N n)) (Fin (D n) × Fin (N n)) ℂ,
    ∃ P : (n : ℕ) → Fin 20000 →
      Matrix (Fin (N n) × Fin (D n)) (Fin (N n) × Fin (D n)) ℂ,
      (∀ n, IsDensityMatrix (ρ n) ∧ IsPOVM (P n)) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, ∀ (_ : NeZero m), 3 ≤ m → m ≤ n →
        1 - 1 / (n : ℝ) ^ C ≤ properColoringProb m (ρ n) (P n) := by sorry

end QuantumSymmetryBreaking.CycleColoring.Supplement
