-- Prove2me | Theorems.Thm_TIESharp_lemma_5_2
-- name    : TIESharp.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:41:39.172059+00:00
-- url     : https://prove2.me/theorems/279e87d7-80ab-4708-8d61-952aa3ad7d70
-- title:
--   Lemma 5.2 — range of a load: width at most $d_i$, and $d_i\le2\,\mathrm{OPT}$
-- statement:
--   Let $n\ge2$ and $t$ a nonnegative profile, with the Bounded-Square probabilities $q$. For the distribution produced by slot rounding, machine $i$'s load is supported in an interval of width at most
--   $$d_i=\max\{t_{ij}: q_{ij}>0\},$$
--   with $d_i=0$ if $q_{ij}=0$ for every job $j$. If $T=\mathrm{OPT}(t)>0$, then $d_i\le2T$.
--
--   The cost ordering prevents successive slots from covering the same range of processing times twice, so the matching controls which jobs a machine can receive together.
--
--   Differences from the source:
--   - generalization: the distribution produced by slot rounding → every slot-feasible assignment has machine i's load in one interval [a, a + d_i]; reason: every assignment in the support of every decomposition (Sec. 5.2) is slot-feasible
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Lemma 5.2, p.23

import Mathlib
import Definitions.Def_TIESharp_Nonneg
import Definitions.Def_TIESharp_opt
import Definitions.Def_TIESharp_SlotFeasible
import Definitions.Def_TIESharp_dMax

set_option autoImplicit false

namespace TIESharp

/-- **Lemma 5.2 (Range of a load)** (Li, *Sharp Bounds for Truthful-in-Expectation Scheduling*,
arXiv:2611.05134, Lemma 5.2, p.23). For the distribution produced by slot rounding, machine `i`'s
load is supported in an interval of width at most `d_i = max{t_ij : q_ij > 0}`, with `d_i = 0` if
`q_ij = 0` for every job `j`. If `T = OPT(t) > 0`, then `d_i ≤ 2T`.

**Formalization Note.** `n ≥ 2` is the standing assumption of §§3–5 (p.4). The interval
`[a, a + d_i]` contains the load of every slot-feasible assignment (`SlotFeasible`), which includes
the support of every slot-rounding law (`IsBSSlotLaw`). `q` is the Bounded-Square rule. -/
theorem lemma_5_2 (n m : ℕ) (hn : 2 ≤ n) (t : Fin n → Fin m → ℝ) (ht : Nonneg t) (i : Fin n) :
    (∃ a : ℝ, ∀ A : Fin m → Fin n, SlotFeasible t A →
      a ≤ MatousekLP.Scheduling.load (Matrix.of t) A i ∧
        MatousekLP.Scheduling.load (Matrix.of t) A i ≤ a + dMax t i) ∧
    (0 < opt t → dMax t i ≤ 2 * opt t) := by sorry

end TIESharp
