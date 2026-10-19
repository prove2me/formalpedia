-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P15_entropicContinuity
-- name    : QAlgorithms.Papers.Independent.Frontier18.P15.entropicContinuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:04:37.58752+00:00
-- url     : https://prove2.me/theorems/90dd32af-58c4-4ef6-b659-8f200fc4041b
-- title:
--   Continuity of the entropic quantities
-- statement:
--   Let $A,B,X$ be finite quantum systems of positive dimensions $a,b,x$, and put $d=abx$. For a density operator $\rho$ on $A\otimes B\otimes X$, let $F(\rho)$ be any of the five quantities $H(ABX)$, $H(A\mid BX)$, $I(A;BX)$, $I(A\rangle BX)$, or $I(A;B\mid X)$, with all entropies measured in bits. One-dimensional factors include the bipartite quantities of the lemma.
--
--   There are a function $\eta:[0,\infty)\to\mathbb R$ with $\lim_{\epsilon\downarrow0}\eta(\epsilon)=0$ and a constant $K>0$, chosen independently of the systems, states, and quantity, such that for all density operators $\rho,\sigma$ and all $\epsilon\ge0$,
--
--   $$
--   \|\rho-\sigma\|_1\le\epsilon\quad\Longrightarrow\quad |F(\rho)-F(\sigma)|\le\eta(\epsilon)+K\epsilon\log_2d.
--   $$
--
--   This is the dimension-uniform continuity estimate for the finite entropy combinations introduced on page 7. The norm is the full trace norm.
-- source:
--   A Resource Framework for Quantum Shannon Theory, arXiv:quant-ph/0512015v1, PDF p. 8, Lemma 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P15

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Frontier18.P15

/-- Lemma 2.1, PDF p.8: dimension-uniform continuity of the entropic quantities on p.7.
The modulus and constant are conclusions, chosen before dimensions, states and error.
The limit is from nonnegative errors. Null systems have dimension one. -/
theorem entropicContinuity :
    ∃ (eta : ℝ → ℝ) (K : ℝ), 0 < K ∧
      Filter.Tendsto eta (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      ∀ (quantity : EntropicQuantity) (a b x : ℕ),
        0 < a → 0 < b → 0 < x →
        ∀ (rho sigma : Matrix (Fin a × (Fin b × Fin x))
          (Fin a × (Fin b × Fin x)) ℂ),
          IsDensityMatrix rho → IsDensityMatrix sigma →
          ∀ epsilon : ℝ, 0 ≤ epsilon → traceNorm (rho - sigma) ≤ epsilon →
            |entropicValue quantity rho - entropicValue quantity sigma| ≤
              eta epsilon + K * epsilon * Real.logb 2 (a * b * x : ℕ) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P15

end
