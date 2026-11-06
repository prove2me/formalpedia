-- Prove2me | Theorems.Thm_StrongConv_limsup_abs_nuAdj_X_pow_le_rhoStair
-- name    : StrongConv.limsup_abs_nuAdj_X_pow_le_rhoStair
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T01:06:54.238936+00:00
-- url     : https://prove2.me/theorems/a8618a2f-d309-4cb8-9f61-291c3ce9ce63
-- title:
--   Lemma 8.5 — limsup |νₘ(xᵖ)|^{1/p} ≤ ρₘ for random regular graphs, 2 ≤ m ≤ d
-- statement:
--   Let $2 \le m \le d$. Let $\nu_m(h)$ (`nuAdj d m h`) be the $m$-th coefficient of the expansion of $\mathbf E[\mathrm{tr}_N\, h(A^N)]$ in powers of $1/N$, where $A^N = \sum_{i=1}^d (S_i^N + S_i^{N*})$ is the adjacency matrix of the random $2d$-regular permutation-model graph on $N$ vertices restricted to $\{1_N\}^\perp$ and $\mathrm{tr}_N$ is the trace divided by $N$. Put $\rho_m = 2\sqrt{2d-1}$ if $2m - 1 \le \sqrt{2d-1}$ and $\rho_m = 2m - 1 + \frac{2d-1}{2m-1}$ otherwise (`rhoStair d m`). Then the sequence $|\nu_m(x^p)|^{1/p}$ is eventually bounded above and
--   $$\limsup_{p \to \infty} |\nu_m(x^p)|^{1/p} \le \rho_m.$$
--   The boundedness conjunct makes the real-valued limit superior the usual one; the paper's statement takes it for granted.
--
--   This is Lemma 8.5 of C.-F. Chen, J. Garza-Vargas, J. A. Tropp and R. van Handel, *A new approach to strong convergence*, Ann. of Math. 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, p. 25): “**Lemma 8.5.** *Define $\rho_m$ as in Theorem 3.6. Then for any $2 \le m \le d$, we have $\limsup_{p\to\infty} |\nu_m(x^p)|^{1/p} \le \rho_m$.*” Its proof (pp. 25–26) combines results of Puder (*Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x, §5.5 and the second theorem of §2.4), stated as `Puder.wordCoeff_eq_zero_and_eq_ncard_crit_and_abs_le` and `Puder.limsup_sum_ncard_crit_rpow_eq_rhoStair`, on the coefficients of the $1/N$-expansion of $\mathbf E[\mathrm{tr}_N\, w(\boldsymbol S^N)]$ in terms of the primitivity rank of the word $w$. The mission's Corollary 8.6 (`StrongConv.supp_subset_Icc_rhoStair_of_extends_nuAdj`) follows from it for $2 \le m \le d$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 25, Lemma 8.5

import Mathlib
import Definitions.Def_StrongConv

open Filter Polynomial

namespace StrongConv

theorem limsup_abs_nuAdj_X_pow_le_rhoStair (d m : ℕ) (hm : 2 ≤ m) (hmd : m ≤ d) :
    IsBoundedUnder (· ≤ ·) atTop (fun p : ℕ => |nuAdj d m (X ^ p)| ^ (1 / (p : ℝ))) ∧
      limsup (fun p : ℕ => |nuAdj d m (X ^ p)| ^ (1 / (p : ℝ))) atTop ≤ rhoStair d m := by
  sorry

end StrongConv
