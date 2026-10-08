-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Transient_lemma_3
-- name    : VeinottSensitiveDP.Transient.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:17.537987+00:00
-- url     : https://prove2.me/theorems/dda2434f-4870-4eb8-8518-83da1fb3ac2e
-- title:
--   Lemma 3 (Hoffman) — a positively similar program has max_g ‖P̃(g)‖ < max_g |σ(P(g))| + ε
-- statement:
--   Let $(r(\cdot),P(\cdot))$ be any dynamic program as in §2 of Veinott (1969): finitely many states, finite nonempty action sets, real rewards and nonnegative transition weights, with no bound on the row sums. For every $\varepsilon>0$ there is a positively similar dynamic program $(\tilde r(\cdot),\tilde P(\cdot))$ such that
--
--   $$\max_{g\in F}\|\tilde P(g)\|<\max_{g\in F}|\sigma(P(g))|+\varepsilon,$$
--
--   where $\|\cdot\|$ is the maximum absolute row sum and $|\sigma(\cdot)|$ the spectral radius.
--
--   A single positive diagonal rescaling thus brings the norms of all transition matrices, simultaneously, to within $\varepsilon$ of the largest spectral radius. The bound cannot be sharpened to equality (the matrix with rows $(1,1)$ and $(0,1)$ has spectral radius $1$ but every positively similar matrix has norm larger than $1$). It is the step from transience of every stationary policy to a uniform geometric bound on all products $P^N(\pi)$.
--
--   **Formalization Note.** The comparison is made in $[0,\infty]$, where Mathlib's spectral radius takes values; the left side is the real maximum norm embedded there. Both sides are finite.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1638, Lemma 3

import Mathlib
import Definitions.Def_VeinottSensitiveDP_Transient_Model
import Definitions.Def_VeinottSensitiveDP_Transient_Similarity

namespace VeinottSensitiveDP.Transient

open Matrix

variable {St : Type} [Fintype St] [DecidableEq St] [Nonempty St] {A : St → Type}
  [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]

/-- **Lemma 3 (Hoffman)** (Veinott, *Discrete Dynamic Programming with Sensitive Discount Optimality Criteria*,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1638).
For every `ε > 0` and every dynamic program `(r(·), P(·))`, there is a positively similar dynamic
program `(r̃(·), P̃(·))` for which `max_g ‖P̃(g)‖ < max_g |σ(P(g))| + ε`.

**Formalization Note.** `max_g` ranges over the finite set `F` of decision rules. `‖·‖` is the
maximum absolute row sum and `|σ(·)|` the spectral radius over `ℂ`; the comparison is made in
`ℝ≥0∞`, where the spectral radius lives (both sides are finite). No transience and no row-sum bound
is assumed: the program is any one with nonnegative weights. -/
theorem lemma_3 (D : Program St A) (ε : ℝ) (hε : 0 < ε) :
    ∃ D' : Program St A, D'.PositivelySimilar D ∧
      ENNReal.ofReal (Finset.univ.sup' Finset.univ_nonempty
          fun g : DecisionRule St A => rowSumNorm (D'.Pmat g)) <
        Finset.univ.sup' Finset.univ_nonempty (fun g : DecisionRule St A => specRad (D.Pmat g)) +
          ENNReal.ofReal ε := by sorry

end VeinottSensitiveDP.Transient
