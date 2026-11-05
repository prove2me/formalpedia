-- Prove2me | Theorems.Thm_StrongConv_exists_uniformExp_trN_wordEval_eq_div
-- name    : StrongConv.exists_uniformExp_trN_wordEval_eq_div
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:42:36.591192+00:00
-- url     : https://prove2.me/theorems/07c99fee-71cd-4696-940a-94b476779be7
-- title:
--   Lemma 5.1 — the expected trace of a word is a rational function of 1/N
-- statement:
--   Let $d \ge 0$ and $q \ge 1$, and let $w$ be a word of length at most $q$ in the letters $g_0 = e$, $g_i$, $g_{d+i} = g_i^{-1}$. Then $g_q(x) = \prod_{j=1}^{q-1}(1 - jx)^{\min(d, \lfloor q/(j+1)\rfloor)}$ has degree at most $q(1 + \log d)$, and there is a real polynomial $f_w$ of degree at most $q(1 + \log d)$ such that for every $N \ge q$
--   $$\mathbf E[\mathrm{tr}_N\, w(\boldsymbol S^N)] = \frac{f_w(1/N)}{g_q(1/N)}.$$
--   Here $\boldsymbol S^N$ are $d$ i.i.d. uniform random permutation matrices restricted to $\{1_N\}^\perp$, and $\mathrm{tr}_N$ is the trace divided by $N$ (Remark 3.3). The paper's $q$ is a length bound in $\mathbb N = \{1, 2, \dots\}$; at $q = 0$ the empty word would give $1 - \frac1N$, of degree $1$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), pp. 19–20, Lemma 5.1

import Mathlib
import Definitions.Def_StrongConv

open Polynomial

namespace StrongConv

theorem exists_uniformExp_trN_wordEval_eq_div (d q : ℕ) (hq : 1 ≤ q) (w : List (Letter d))
    (hw : w.length ≤ q) :
    ((gPoly d q).natDegree : ℝ) ≤ q * (1 + Real.log d) ∧
      ∃ f : ℝ[X], (f.natDegree : ℝ) ≤ q * (1 + Real.log d) ∧
        ∀ N : ℕ, q ≤ N →
          uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (wordEval (sModel σ) w)) =
            f.eval (1 / (N : ℝ)) / (gPoly d q).eval (1 / (N : ℝ)) := by
  sorry

end StrongConv
