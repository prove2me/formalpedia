-- Prove2me | Theorems.Thm_PerishBaseStock_Lifo_lemma_3
-- name    : PerishBaseStock.Lifo.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:10.439526+00:00
-- url     : https://prove2.me/theorems/119ecca7-364f-4511-a424-34e3b04e2a9b
-- title:
--   Lemma 3 — $\hat C_L(S)\le C^{LIFO}(S)\le\hat C_U(S)$
-- statement:
--   In the LIFO perishable inventory system with lifetime $m\ge 1$ and costs $h>0$, $p>0$, $\theta\ge 0$, let $C^{LIFO}(S)$ be the long-run average cost of the base-stock policy $\pi_S$. For every $S\ge 0$,
--   $$\hat C_L(S)\le C^{LIFO}(S)\le\hat C_U(S),$$
--   where
--   $$\hat C_L(S)=h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]+\frac{\theta}{m}\mathbb E[(S-\max\{D_1,\dots,D_m\})^+],\qquad \hat C_U(S)=\Big(h+\frac{\theta}{m}\Big)\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+].$$
--
--   The two explicit bounds replace the intractable cost of a base-stock policy in the LIFO system; their average defines the heuristic level $\hat S$, and the upper bound drives every gap estimate of Theorem 5.
--
--   **Formalization Note** $C^{LIFO}(S)$ is the limsup average of the simulated period costs of $\pi_S$, valued in $[0,\infty]$; the real bounds enter through `ENNReal.ofReal`, which is faithful because both are nonnegative.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 16, Lemma 3, (11)–(12)

import Definitions.Def_PerishBaseStock_Lifo_Heuristic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace PerishBaseStock.Lifo

/-- Lemma 3: `Ĉ_L(S) ≤ C^{LIFO}(S) ≤ Ĉ_U(S)` for every `S ≥ 0`. -/
theorem lemma_3 (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing) (S : ℝ≥0) :
    ENNReal.ofReal (hatCL P c S) ≤ baseStockCost P c S ∧
      baseStockCost P c S ≤ ENNReal.ofReal (hatCU P c S) := by sorry

end PerishBaseStock.Lifo
