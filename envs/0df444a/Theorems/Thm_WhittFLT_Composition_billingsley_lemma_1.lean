-- Prove2me | Theorems.Thm_WhittFLT_Composition_billingsley_lemma_1
-- name    : WhittFLT.Composition.billingsley_lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:58:08.710865+00:00
-- url     : https://prove2.me/theorems/8c02f69f-dd14-491e-a4d0-832411a1f0bd
-- title:
--   Billingsley's small-oscillation partition lemma (cited in Theorem 3.1)
-- statement:
--   Let $c<d$, let $x$ be a càdlàg path from $[c,d]$ into a metric space $(S,m)$, and let $\varepsilon>0$. There is a finite partition $c=t_0<t_1<\cdots<t_n=d$ such that, on every half-open piece,
--
--   $$
--   \sup_{t_{j-1}\le s_1,s_2<t_j}m(x(s_1),x(s_2))<\varepsilon
--   \qquad(1\le j\le n).
--   $$
--
--   This is the compactness property of càdlàg paths used in Whitt's proof of Theorem 3.1(ii). Whitt cites it as Lemma 1 on p. 110 of Billingsley (1968); it is not a numbered theorem of Whitt's paper.
--
--   **Formalization Note** The supremum is taken in the extended nonnegative reals over exactly the half-open intervals printed in the source. The strict inequality includes the positive threshold and guarantees the oscillation is finite.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), §3, proof of Theorem 3.1(ii), p. 75 (citing Billingsley 1968, Lemma 1, p. 110); https://doi.org/10.1287/moor.5.1.67

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD

namespace WhittFLT.Composition

open Set Filter Topology
open scoped ENNReal

/-- The finite small-oscillation partition used in §3, proof of Theorem 3.1(ii), p. 75;
Whitt cites Billingsley (1968), Lemma 1, p. 110. -/
theorem billingsley_lemma_1 {S : Type*} [MetricSpace S] (c d : ℝ) (hcd : c < d)
    (x : ℝ → S) (hx : IsCadlagOn (Icc c d) x) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (t : Fin (n + 1) → ℝ), t 0 = c ∧ t (Fin.last n) = d ∧ StrictMono t ∧
      ∀ j : Fin n, (⨆ s₁ ∈ Ico (t j.castSucc) (t j.succ), ⨆ s₂ ∈ Ico (t j.castSucc) (t j.succ),
        edist (x s₁) (x s₂)) < ENNReal.ofReal ε := by sorry

end WhittFLT.Composition
