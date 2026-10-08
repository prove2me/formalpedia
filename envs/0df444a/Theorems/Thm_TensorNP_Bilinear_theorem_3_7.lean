-- Prove2me | Theorems.Thm_TensorNP_Bilinear_theorem_3_7
-- name    : TensorNP.Bilinear.theorem_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:50.968753+00:00
-- url     : https://prove2.me/theorems/f0fa7266-0862-45bf-a514-1d4492b1baa6
-- title:
--   Theorem 3.7 — 3-colorability reduces to tensor bilinear feasibility over $\mathbb R$ and over $\mathbb C$
-- statement:
--   Let $F = \mathbb R$ or $F = \mathbb C$. Graph 3-colorability is polynomial-time many-one reducible to tensor bilinear feasibility over $F$ (Problem 3.1): there is a function $f$, computable by a Turing machine in time polynomial in the length of its input, such that for every binary word $x$,
--   $$
--   x \in \textsf{3-COLORABILITY} \iff f(x) \in \textsf{TBF}_F ,
--   $$
--   where $\textsf{TBF}_F$ is the language of codes of rational tensors $\mathcal A \in \mathbb Q^{l\times m\times n}$ for which (9) has a solution with $\mathbf u\in F^l$, $\mathbf v\in F^m$, $\mathbf w\in F^n$ all nonzero. The statement asserts this for $F = \mathbb R$ and for $F = \mathbb C$.
--
--   Since 3-colorability is NP-complete (Karp 1972), tensor bilinear feasibility is NP-hard over $\mathbb R$ and over $\mathbb C$; that consequence is cited by the paper and is not part of the formal statement.
--
--   **Formalization Note** The paper's §1.4 calls a problem polynomially reducible to another in the oracle (Cook) sense; the statement here is the stronger many-one (Karp) reducibility of the published definition `CookPvsNP.PolyReducible`, which is what the paper's proof constructs. Graphs and rational tensors are coded in binary as in `TensorNP.Bilinear.Encoding`. Polynomial-time computability refers to Cook's one-tape Turing machines. The reduction must map every word, including words that are not graph codes, and must handle the empty graph, for which the paper's tensor $\mathcal A_G$ has no slices.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:17, Theorem 3.7 and its proof

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_TensorNP_Bilinear_Encoding

namespace TensorNP.Bilinear

open CookPvsNP

/-- Theorem 3.7 (p. 0:17): graph 3-colorability is polynomial-time many-one reducible to tensor
bilinear feasibility (Problem 3.1), over `ℝ` and over `ℂ`. -/
theorem theorem_3_7 :
    PolyReducible TensorNP.Eigen.threeColLang (tbfLang ℝ) ∧ PolyReducible TensorNP.Eigen.threeColLang (tbfLang ℂ) := by sorry

end TensorNP.Bilinear
