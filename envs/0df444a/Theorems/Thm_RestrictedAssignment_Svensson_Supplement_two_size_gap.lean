-- Prove2me | Theorems.Thm_RestrictedAssignment_Svensson_Supplement_two_size_gap
-- name    : RestrictedAssignment.Svensson.Supplement.two_size_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:00:22.752787+00:00
-- url     : https://prove2.me/theorems/0073bf4a-3e71-4184-ab16-13609adebc56
-- title:
--   Theorem 3.1 — two-size configuration-LP integrality gap
-- statement:
--   Let $J,M$ be arbitrary finite job and machine sets, let $\Gamma(j)\subseteq M$ be the allowed machines, let $\varepsilon\ge0$, and let $T\ge0$ be a target makespan. Suppose every job size is either $\varepsilon T$ (a small job) or $T$ (a big job), and that the configuration LP is feasible for target $T$. Then there is an eligible total schedule $\sigma:J\to M$ with
--   $$\sum_{j:\,\sigma(j)=i}p_j\le(5/3+\varepsilon)\,T\qquad(i\in M).$$
--   At $T=1$ this is the paper's setting verbatim: small jobs of size $\varepsilon$, big jobs of size $1$, and [C-LP] feasible for target $1$, giving a schedule of makespan at most $1+R$ with $R=2/3+\varepsilon$. The general $T$ is the same statement in other units. The boundary $\varepsilon=0$ is retained and $\varepsilon$ has no upper bound.
--
--   This companion result is the paper's improved two-size bound, proved in Section 3 independently of the general 33/17 goal. No termination or complexity assumption is attached to the schedule-existence conclusion.
--
--   Differences from the source:
--   - encoding: configuration-LP integrality gap at most 5/3 + ε for sizes ε ≥ 0 and 1 → every target T ≥ 0 for which [C-LP] is feasible admits an eligible schedule with each load at most (5/3 + ε)T; reason: the target formulation expresses OPT ≤ (5/3 + ε)·OPT_LP without dividing by an optimum (OPT_LP is attained because there are finitely many configurations)
--   - reading: sizes ε and 1 → sizes εT and T, i.e. sizes ε and 1 in units of the LP target; reason: the paper assumes throughout (p. 3) that OPT_LP = 1, obtained by scaling processing times, and its proof of Theorem 3.1 uses it (proof of Claim 3.8, p. 9 — a big job of size 1 is alone in a configuration). Sizes ε and 1 with an unrelated target in (1, 3/2) are not covered by the paper's argument
--   - encoding: finite restricted-assignment instances → arbitrary finite job and machine types, including empty sets; reason: LP feasibility already forces every job to have an allowed machine, and zero targets and zero-size jobs remain included
-- source:
--   Svensson, Santa Claus Schedules Jobs on Unrelated Machines, arXiv:1011.1168v2, p. 4, Theorem 3.1

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP

namespace RestrictedAssignment.Svensson.Supplement

/-- Svensson, arXiv:1011.1168v2, p. 4, Theorem 3.1, under the paper's standing
normalization (p. 3: "we will assume throughout the paper that OPT_LP = 1 ... by scaling
processing times"): the small jobs have size `ε` and the big jobs size `1` in units of the
LP target. Stated scale-free: with target `T ≥ 0`, every size is `ε * T` or `T`; if [C-LP]
is feasible for `T`, some schedule respecting `Γ` has every load at most `(5/3 + ε) * T`.
At `T = 1` this is the paper's statement verbatim; `ε ≥ 0` has no upper bound. -/
theorem two_size_gap {J M : Type} [Fintype J] [Fintype M]
    [DecidableEq J] [DecidableEq M] (Γ : J → Finset M) (p : J → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (T : ℝ) (hT : 0 ≤ T)
    (hsizes : ∀ j, p j = ε * T ∨ p j = T) (hLP : CLPFeasible Γ p T) :
    ∃ σ : J → M, (∀ j, σ j ∈ Γ j) ∧
      ∀ i, schedLoad p σ i ≤ (5 / 3 + ε) * T := by sorry

end RestrictedAssignment.Svensson.Supplement
