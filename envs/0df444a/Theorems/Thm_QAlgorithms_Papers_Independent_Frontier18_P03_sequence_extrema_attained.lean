-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P03_sequence_extrema_attained
-- name    : QAlgorithms.Papers.Independent.Frontier18.P03.sequence_extrema_attained
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:30:45.637172+00:00
-- url     : https://prove2.me/theorems/b0e37da4-e30f-4ba1-a0b6-5dc4e7681f59
-- title:
--   Attainment of the four sequence cutoffs
-- statement:
--   Let $F_n$ be a nonempty family of monotone nondecreasing functions $\mathbb R\to\mathbb R$, and put $\mathcal F=\prod_{n\ge1}F_n$. Fix $x\in\mathbb R$. For $f=(f_n)\in\mathcal F$, define the extended-real cutoffs $$L_x(f)=\sup\{a\in\mathbb R:\limsup_n f_n(a)\le x\},\qquad U_x(f)=\inf\{a\in\mathbb R:\liminf_n f_n(a)\ge x\}.$$ Then all four extrema $$\max_{f\in\mathcal F}L_x(f),\quad\max_{f\in\mathcal F}U_x(f),\quad\min_{f\in\mathcal F}L_x(f),\quad\min_{f\in\mathcal F}U_x(f)$$ are attained, allowing $-\infty$ and $+\infty$. The four optimizing sequences may differ.
--
--   This attainment principle applies to unrestricted sequences of spectral-distribution functions.
--
--   **Formalization Note** Both the inner limits and outer cutoffs use extended reals. The Lean index $n$ denotes source index $n+1$.
-- source:
--   General formulas for capacity of classical-quantum channels, arXiv:quant-ph/0206186v4, PDF p. 8, Lemma 1; Appendix I, pp.30–31

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P03

noncomputable section

open Filter

namespace QAlgorithms.Papers.Independent.Frontier18.P03

/-- Lemma 1, PDF p.8; Appendix I, pp.30–31. All four extrema are attained,
possibly by four different sequences. There is no boundedness or continuity
assumption on the real-valued monotone functions. -/
theorem sequence_extrema_attained
    (F : ℕ → Set (ℝ → ℝ))
    (hne : ∀ n, (F n).Nonempty)
    (hmono : ∀ n, ∀ f ∈ F n, Monotone f) (x : ℝ) :
    (∃ f : FunctionChoices F,
      IsGreatest (Set.range fun g : FunctionChoices F => minusCutoff g.val x)
        (minusCutoff f.val x)) ∧
    (∃ f : FunctionChoices F,
      IsGreatest (Set.range fun g : FunctionChoices F => plusCutoff g.val x)
        (plusCutoff f.val x)) ∧
    (∃ f : FunctionChoices F,
      IsLeast (Set.range fun g : FunctionChoices F => minusCutoff g.val x)
        (minusCutoff f.val x)) ∧
    (∃ f : FunctionChoices F,
      IsLeast (Set.range fun g : FunctionChoices F => plusCutoff g.val x)
        (plusCutoff f.val x)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P03

end
