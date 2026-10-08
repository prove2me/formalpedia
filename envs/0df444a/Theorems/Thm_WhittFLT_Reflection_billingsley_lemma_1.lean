-- Prove2me | Theorems.Thm_WhittFLT_Reflection_billingsley_lemma_1
-- name    : WhittFLT.Reflection.billingsley_lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:13.410635+00:00
-- url     : https://prove2.me/theorems/00ebb8cb-6b74-4d1e-9b7e-1acc3a785b78
-- title:
--   §4, proof of Theorem 4.1, p. 79 — Billingsley’s Lemma 1 (cited)
-- statement:
--   Let $x\in D([c,d],S)$ with $c<d$, and let $\varepsilon>0$. There is a finite partition $c=t_0<\cdots<t_n=d$ such that the oscillation of $x$ on every half-open interval of the partition is below $\varepsilon$:
--
--   $$
--   \sup_{t_{j-1}\le s_1,s_2<t_j}m(x(s_1),x(s_2))<\varepsilon\qquad(1\le j\le n).
--   $$
--
--   This is the one-path partition fact cited from Billingsley in Whitt’s addition argument.
--
--   **Formalization Note** The path is a total function on $\mathbb R$ restricted to $[c,d]$; the oscillation is an extended nonnegative supremum.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), §4, proof of Theorem 4.1, p. 79; citing Billingsley (1968), Lemma 1, p. 110

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD

namespace WhittFLT.Reflection

open Set Filter Topology
open scoped ENNReal

/-- Billingsley (1968), Lemma 1, p. 110, as cited in Whitt's proof of Theorem 4.1, p. 79. -/
theorem billingsley_lemma_1 {S : Type*} [MetricSpace S] (c d : ℝ) (hcd : c < d)
    (x : ℝ → S) (hx : WhittFLT.Composition.IsCadlagOn (Icc c d) x) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (t : Fin (n + 1) → ℝ), t 0 = c ∧ t (Fin.last n) = d ∧ StrictMono t ∧
      ∀ j : Fin n, (⨆ s₁ ∈ Ico (t j.castSucc) (t j.succ), ⨆ s₂ ∈ Ico (t j.castSucc) (t j.succ),
        edist (x s₁) (x s₂)) < ENNReal.ofReal ε := by sorry

end WhittFLT.Reflection
