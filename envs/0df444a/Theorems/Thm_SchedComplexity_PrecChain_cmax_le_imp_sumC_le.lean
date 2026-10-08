-- Prove2me | Theorems.Thm_SchedComplexity_PrecChain_cmax_le_imp_sumC_le
-- name    : SchedComplexity.PrecChain.cmax_le_imp_sumC_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:15:11.963055+00:00
-- url     : https://prove2.me/theorems/671a7734-2650-4424-b79e-91434de0f385
-- title:
--   Proof of Theorem 1(l), first line — C_max ≤ y' implies a schedule of the construction with Σ C_j ≤ y
-- statement:
--   Let $p_*$ be a natural number, $I$ an instance of $n'|m|I,\mathit{prec},1\le p_{j1}\le p_*$ with $n'$ jobs, and $y'$ a natural number with $y' \le n'p_*$. Let $n'' = (n'-1)y'$, $n = n'+n''$, $y = ny' + \tfrac12 n''(n''+1)$, and let $I^+$ be the instance obtained by adding $n''$ unit jobs $J_{n'+k}$ with $J_j < J_{n'+k}$ for $j = 1, \dots, n'+k-1$ (the construction `SchedComplexity.PrecChain.Construction`).
--
--   If $I$ has a feasible schedule with $C_{\max} \le y'$, then $I^+$ has a feasible schedule with
--
--   $$\sum_{j=1}^{n} C_j \le y.$$
--
--   This is the "only if" half of the equivalence "$P'$ has a solution with value $\le y'$ if and only if $P$ has a solution with value $\le y$".
--
--   **Formalization Note** The paper prints the intermediate bound $n'y' + \sum_{k=n'+1}^{n}(y'+k) = y$; the index range of the sum is a misprint for $k = 1, \dots, n''$ (the added jobs), since only that range gives $y$. The Lean states the end-to-end bound $\sum_j C_j \le y$, with $y$ computed in $\mathbb Q$ exactly as printed. "$C_{\max} \le y'$" is "$C_j \le y'$ for every job".
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 9, proof of Theorem 1(l), first line of the display

import Mathlib
import Definitions.Def_SchedComplexity_PrecChain_Model
import Definitions.Def_SchedComplexity_PrecChain_Construction

namespace SchedComplexity.PrecChain

/-- Brucker, Lenstra & Rinnooy Kan (1975), proof of Theorem 1(l), p. 9, first line of the
display: `C_max ≤ y' ⇒ Σ_{j=1}^{j=n} C_j ≤ n'y' + Σ (y' + k) = y`. For an instance `I` of
`P' = n'|m|I,prec,1≤p_j1≤p_*|C_max` and `0 ≤ y' ≤ n' p_*`: if `I` has a feasible schedule with
`C_max ≤ y'`, the constructed instance `chainExtend I y'` has a feasible schedule with
`Σ_j C_j ≤ y = n y' + ½ n''(n'' + 1)`. (The printed sum runs over `k = n'+1, …, n`; the bound
needs `k = 1, …, n''`, the indices of the added jobs. The statement gives the end-to-end bound
`Σ_j C_j ≤ y`.) -/
theorem cmax_le_imp_sumC_le (pstar : ℕ) (I : Instance) (hI : I.InClass pstar) (y' : ℕ)
    (hy' : y' ≤ I.n * pstar) (h : CmaxYes I y') :
    ∃ σ : Schedule (chainExtend I y'), σ.IsFeasible ∧
      (σ.totalCompletion : ℚ) ≤ chainThresholdQ I.n y' := by sorry

end SchedComplexity.PrecChain
