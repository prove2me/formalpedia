-- Prove2me | Theorems.Thm_PolyEulerFlow_proposition_37
-- name    : PolyEulerFlow.proposition_37
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:32.600502+00:00
-- url     : https://prove2.me/theorems/fc703163-230f-4294-b0a3-f35aacf89eec
-- title:
--   Proposition 37 — resetting halt and an infinite correct tail
-- statement:
--   With the constants of Lemmas 31 and 35: suppose the halting branch is the constant map $Y\mapsto C_{halt}$. For sufficiently large $s$, once a halting cycle is completed, all subsequent sections are admissible above $C_{halt}$ with error at most $B\Delta_\varepsilon$, and at every subsequent micro-step the data are within $C\Delta_\varepsilon$ of $C_{halt}$. This holds for every mesh and every disturbance of level $0\le\nu\le\varepsilon^2$.
--
--   Precisely: if a cycle starts at a state admissible above a valid configuration $C$ whose selected branch is the constant map $Y\mapsto C_{halt}$, with $C_{halt}$ valid and selecting the same constant branch, then all phase entries of the execution exist, every section $j\ge1$ is admissible above $C_{halt}$ with $\|Y-C_{halt}\|_\infty\le B\Delta_\varepsilon$, and $\|Y-C_{halt}\|_\infty\le C\Delta_\varepsilon$ at every index after the first section.
--
--   The halting configuration absorbs errors: its branch has zero linear part, so the cycle lemma applies forever without accumulation, which gives a stable readout.
--
--   Differences from the source:
--   - generalization: every mesh 0 < η ≤ 1 (one constant step) → every variable mesh 0 < η_k ≤ 1 with Σ η_k = ∞; reason: Corollary 39 (p.34) states that every clock, cut and cycle estimate holds on such meshes; every constant step in (0, 1] is one of them
--   - reading: once a halting cycle is completed → a cycle started (at index 0) at a state admissible above a valid C whose selected branch is Y ↦ C_halt, with C_halt valid and selecting the same constant branch; completed at its first section; reason: the resetting halt of Definition 13
--   - reading: for sufficiently large s; C∆ε → a threshold s₁ and a constant C_mic existential with Lemma 35's constants; reason: standard reading
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Proposition 37, p.33 (PDF 35)

import Mathlib
import Definitions.Def_PolyEulerFlow_IsCycleConstants

namespace PolyEulerFlow

/-- **Proposition 37 (Resetting halt and an infinite correct tail)**, p.33 (PDF 35). Bournez, One Polynomial Field for Every Euler Step and
the Flow (manuscript, sha256 c4e01b2b…).

With the constants of Lemmas 31 and 35: suppose the halting branch is the constant map `Y ↦ C_halt`. For sufficiently large `s`, once a halting
cycle is completed, all the subsequent sections are admissible above `C_halt` with error at most `B∆ε`, and at every subsequent micro-step the data
are within `C∆ε` of `C_halt`; this holds for every mesh and every disturbance of the permitted size `0 ≤ ν ≤ ε²`.

**Formalization Note** A halting cycle is a cycle that starts (at index `0`) at a state admissible above a valid configuration `C` whose selected branch
is the constant map `Y ↦ C_halt`, with `C_halt` valid and its own selected branch the same constant map (the resetting halt of Definition 13). It is
completed at its section `kk 4`; the subsequent sections are `kk (4j)`, `j ≥ 1`. The mesh is variable (Corollary 39, p.34). -/
theorem proposition_37 :
    ∃ A0 B0 Cdur Cenv Cnext Dclk ε0 : ℝ, IsUniformClock A0 B0 Cdur Cenv Cnext Dclk ε0 ∧
    ∀ (m g : ℕ) (prog : SeparatedAffineProgram m g) (K : ℕ), 256 ≤ K →
      ∃ (A B : ℝ) (s0 : ℕ) (lo hi : CompiledState m g) (Ccyc Cmic : ℝ) (s1 : ℕ), 0 < s0 ∧ 0 < Cmic ∧
        IsCycleConstants prog K A0 B0 A B s0 lo hi Ccyc ∧
        ∀ s : ℕ, s1 ≤ s →
          let h := scale s
          let ε := h ^ K
          ∀ (ν : ℝ) (C Chalt : Fin m → ℝ) (Z0 : CompiledState m g), 0 ≤ ν → ν ≤ ε ^ 2 →
            C ∈ prog.valid h → Chalt ∈ prog.valid h →
            prog.IsConstantBranch (prog.signPat h C) Chalt → prog.IsConstantBranch (prog.signPat h Chalt) Chalt →
            IsAdmissibleAbove prog K A0 B0 A ν h C Z0 →
            ∀ (η : ℕ → ℝ) (ξ : ℕ → CompiledState m g), IsAdmissibleMesh η → IsPermittedDisturbance ν ξ →
              let z := eulerOrbit (compiledField prog K h) Z0 η ξ
              ∃ kk : ℕ → ℕ, IsPhaseEntries phaseBit z 0 kk ∧
                (∀ j, 1 ≤ j → IsAdmissibleAbove prog K A0 B0 A ν h Chalt (z (kk (4 * j))) ∧
                  ‖dataY (z (kk (4 * j))) - Chalt‖ ≤ B * deltaEps ε ν) ∧
                ∀ k, kk 4 ≤ k → ‖dataY (z k) - Chalt‖ ≤ Cmic * deltaEps ε ν := by sorry

end PolyEulerFlow
