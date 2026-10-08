-- Prove2me | Theorems.Thm_SchedComplexity_PrecChain_cmax_gt_imp_sumC_gt
-- name    : SchedComplexity.PrecChain.cmax_gt_imp_sumC_gt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:15:47.02876+00:00
-- url     : https://prove2.me/theorems/8987cbec-b1ae-4f1e-8539-6617307e74a6
-- title:
--   Proof of Theorem 1(l), second line — C_max > y' implies every schedule of the construction has Σ C_j > y
-- statement:
--   Let $p_*$, $I$, $n'$, $y' \le n'p_*$, $n''$, $n$, $y$ and $I^+$ be as in the construction of Theorem 1(l): $n'' = (n'-1)y'$, $n = n'+n''$, $y = ny' + \tfrac12 n''(n''+1)$, and $I^+$ adds $n''$ unit jobs $J_{n'+k}$ with $J_j < J_{n'+k}$ for $j = 1, \dots, n'+k-1$.
--
--   If every feasible schedule of $I$ has $C_{\max} > y'$, then every feasible schedule of $I^+$ satisfies
--
--   $$\sum_{j=1}^{n} C_j > y.$$
--
--   Together with the first line of the display this is the equivalence "$P'$ has a solution with value $\le y'$ if and only if $P$ has a solution with value $\le y$" on which the reduction of Theorem 1(l) rests.
--
--   **Formalization Note** "$C_{\max} > y'$" is read as the negation of the left-hand side of the equivalence: no feasible schedule of $I$ has $C_j \le y'$ for all $j$. The paper prints the intermediate bound $y' + \sum_{k=n'+1}^{n}(y'+1+k) = y$; the index range is a misprint for $k = 1,\dots,n''$, and the Lean states the end-to-end bound $\sum_j C_j > y$, with $y$ in $\mathbb Q$ exactly as printed. The hypothesis that $I$ is in the class (processing times at least $1$) is used by the paper's strict inequality.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 9, proof of Theorem 1(l), second line of the display

import Mathlib
import Definitions.Def_SchedComplexity_PrecChain_Model
import Definitions.Def_SchedComplexity_PrecChain_Construction

namespace SchedComplexity.PrecChain

/-- Brucker, Lenstra & Rinnooy Kan (1975), proof of Theorem 1(l), p. 9, second line of the
display: `C_max > y' ⇒ Σ_{j=1}^{j=n} C_j > y' + Σ (y' + 1 + k) = y`. For an instance `I` of
`P' = n'|m|I,prec,1≤p_j1≤p_*|C_max` and `0 ≤ y' ≤ n' p_*`: if every feasible schedule of `I`
has `C_max > y'` (no feasible schedule has `C_j ≤ y'` for all `j`), then every feasible
schedule of the constructed instance `chainExtend I y'` has `Σ_j C_j > y = n y' + ½ n''(n'' + 1)`.
(The printed sum runs over `k = n'+1, …, n`; the bound needs `k = 1, …, n''`. The statement
gives the end-to-end bound `Σ_j C_j > y`.) -/
theorem cmax_gt_imp_sumC_gt (pstar : ℕ) (I : Instance) (hI : I.InClass pstar) (y' : ℕ)
    (hy' : y' ≤ I.n * pstar) (h : ¬ CmaxYes I y') :
    ∀ σ : Schedule (chainExtend I y'), σ.IsFeasible →
      chainThresholdQ I.n y' < (σ.totalCompletion : ℚ) := by sorry

end SchedComplexity.PrecChain
