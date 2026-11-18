-- Prove2me | Theorems.Thm_WeldedPath_retained_record_recompression
-- name    : WeldedPath.retained_record_recompression
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-17T22:59:18.851088+00:00
-- url     : https://prove2.me/theorems/8c160ed9-420a-4ce6-a9e9-4fab484201c4
-- title:
--   Recompression error when the queried answer is retained
-- statement:
--   For a partial permutation I on s points and a known record I(x)=y, the canonical compression primitive satisfies
--
--   \[\|(pC_x-1)|I\rangle\|^2=\frac{2}{s-|I|+1}.\]
--
--   More generally, let c range over an arbitrary finite coherent control register, let x(c),y(c) be the query and retained answer, and let ψ be supported on pairs (c,I) with I(x(c))=y(c) and |I|≤r≤s. Then
--
--   \[\|\sum_c |c\rangle\langle c|\otimes(pC_{x(c)}-1)\,\psi\|
--   \le \sqrt{\frac{2}{s-r+1}}\,\|\psi\|.\]
--
--   The second bound covers arbitrary coherent superpositions and arbitrary extra information in c. The retained answer is an explicit support condition, not a measurement assumption.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/html/2611.05912v1, Observation 2.5 and Proposition 2.6. The coherent-control version allows the query point to depend on the control.

import Definitions.Def_WeldedPath_exactCpO

set_option autoImplicit false

namespace WeldedPath

universe u

theorem retained_record_recompression :
    ∀ s : ℕ,
      (∀ (I : InjDb s) (x y : Fin s), I x = some y →
        ‖(pC s x - 1) (ket I)‖ ^ 2 = 2 / ((s - I.size + 1 : ℕ) : ℝ)) ∧
      (∀ (C : Type u) [Fintype C] [DecidableEq C]
        (r : ℕ), r ≤ s → ∀ (x y : C → Fin s) (ψ : Hil (C × InjDb s)),
        (∀ c I, ψ (c, I) ≠ 0 → I (x c) = some (y c) ∧ I.size ≤ r) →
        ‖controlled (fun c => pC s (x c) - 1) ψ‖ ≤
          Real.sqrt (2 / ((s - r + 1 : ℕ) : ℝ)) * ‖ψ‖) := by
  sorry

end WeldedPath
