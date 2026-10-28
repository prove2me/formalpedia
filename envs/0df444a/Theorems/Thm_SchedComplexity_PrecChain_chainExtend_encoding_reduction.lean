-- Prove2me | Theorems.Thm_SchedComplexity_PrecChain_chainExtend_encoding_reduction
-- name    : SchedComplexity.PrecChain.chainExtend_encoding_reduction
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T06:41:17.41886+00:00
-- url     : https://prove2.me/theorems/b6a50394-c334-478d-9367-dfec05e6c17e
-- title:
--   Theorem 1(l) — Polynomial-Time Binary Encoding Reduction for Precedence-Constrained Scheduling
-- statement:
--   For every $p_* \ge 1$, there exists a polynomial-time computable function $f$ on $\mathrm{BSym}$ strings that maps $\mathrm{code}(I, y')$ (when $y' \le n' p_*$) to $\mathrm{code}(\mathrm{chainExtend}(I, y'), \mathrm{chainThreshold}(n', y'))$, and maps instances with $y' > n' p_*$ in the class to a yes-instance in $\mathrm{sumCLang}(p_*)$.
-- source:
--   Brucker, Lenstra & Rinnooy Kan 1975, Complexity of Machine Scheduling Problems, Report BW 43/75, p. 9, Theorem 1(l)

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Card
import Mathlib.Data.List.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SchedComplexity_PrecChain_Languages
import Definitions.Def_SchedComplexity_PrecChain_Construction

namespace SchedComplexity.PrecChain

open ProjSchedTW.Complexity (BSym encNats)

/-- Polynomial-time binary encoding reduction for Theorem 1(l) (Brucker, Lenstra & Rinnooy Kan
1975, p. 9): for every `pstar ≥ 1`, there is a polynomial-time computable function `f` on `BSym`
strings that maps `code I y'` (when `y' ≤ I.n * pstar`) to `code (chainExtend I y')
(chainThreshold I.n y')`, and maps `code I y'` with `I.n * pstar < y'` and `I.InClass pstar` to a
yes-instance in `sumCLang pstar`. -/
theorem chainExtend_encoding_reduction (pstar : ℕ) (hpstar : 1 ≤ pstar) :
    ∃ f : List BSym → List BSym, CookPvsNP.PolyTimeComputable f ∧
      ∀ c : List BSym,
        ((∃ (I : Instance) (y' : ℕ), I.InClass pstar ∧ y' ≤ I.n * pstar ∧
            (∃ σ : Schedule (chainExtend I y'), σ.IsFeasible ∧
              (σ.totalCompletion : ℚ) ≤ chainThresholdQ I.n y') ∧
            c = code I y') ∨
          (∃ (I : Instance) (y' : ℕ), I.InClass pstar ∧ I.n * pstar < y' ∧ c = code I y')) ↔
          f c ∈ sumCLang pstar := by sorry

end SchedComplexity.PrecChain
