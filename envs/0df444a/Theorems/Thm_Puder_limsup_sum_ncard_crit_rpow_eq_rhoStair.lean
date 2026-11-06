-- Prove2me | Theorems.Thm_Puder_limsup_sum_ncard_crit_rpow_eq_rhoStair
-- name    : Puder.limsup_sum_ncard_crit_rpow_eq_rhoStair
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T20:43:30.038204+00:00
-- url     : https://prove2.me/theorems/9c33d645-511a-4d26-b94e-7e6e87b73a1a
-- title:
--   Puder, §2.4 — the growth rate of Σ |Crit(w)| over words of length p with π(w) = m is ρₘ
-- statement:
--   Let $d \ge 2$ and $0 \le m \le d$. For $p \ge 0$ let
--   $$c_p = \sum_{\substack{1 \le i_1, \dots, i_p \le 2d \\ \pi(g_{i_1} \cdots g_{i_p}) = m}} |\mathrm{Crit}(g_{i_1} \cdots g_{i_p})|,$$
--   the sum over all $(2d)^p$ words of length $p$ in $g_1, \dots, g_d$ and $g_{d+i} = g_i^{-1}$ whose reduction in $\mathbf F_d$ has primitivity rank $m$ (`Puder.primitivityRank`, `Puder.Crit`; the word is `List.ofFn` of the letters, reduced by `StrongConv.wordFree`). Then the sequence $c_p^{1/p}$ is eventually bounded above and
--   $$\limsup_{p \to \infty} c_p^{1/p} = \rho_m,$$
--   where $\rho_m = 2\sqrt{2d-1}$ if $2m - 1 \le \sqrt{2d-1}$ and $\rho_m = 2m - 1 + \frac{2d-1}{2m-1}$ otherwise (`StrongConv.rhoStair d m`). The boundedness conjunct makes the real-valued limit superior the usual one.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 26, the growth-rate theorem of Puder cited in the proof of Lemma 8.5, which cites Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), §2.4 (Section 2, Step IV, of the arXiv version), the second unnumbered theorem, for the bouquet

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder

open Filter

namespace Puder

theorem limsup_sum_ncard_crit_rpow_eq_rhoStair (d m : ℕ) (hd : 2 ≤ d) (hm : m ≤ d) :
    IsBoundedUnder (· ≤ ·) atTop (fun p : ℕ =>
        (∑ i : Fin p → Fin d ⊕ Fin d with
            primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (p : ℝ))) ∧
      limsup (fun p : ℕ =>
        (∑ i : Fin p → Fin d ⊕ Fin d with
            primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (p : ℝ))) atTop = StrongConv.rhoStair d m := by
  sorry

end Puder
