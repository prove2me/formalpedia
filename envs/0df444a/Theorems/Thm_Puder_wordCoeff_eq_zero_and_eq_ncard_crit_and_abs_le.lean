-- Prove2me | Theorems.Thm_Puder_wordCoeff_eq_zero_and_eq_ncard_crit_and_abs_le
-- name    : Puder.wordCoeff_eq_zero_and_eq_ncard_crit_and_abs_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T20:43:20.462205+00:00
-- url     : https://prove2.me/theorems/f0a553db-7574-44da-96cd-b8c5ff598142
-- title:
--   Puder, §5.5 — b_s(w) = 0 for s ≤ π(w) − 2, b_{π(w)−1}(w) = |Crit(w)|, |b_s(w)| ≤ q^{2(s+1)} for s ≥ π(w)
-- statement:
--   Let $w$ be a word of length $q$ in the letters $g_0 = e, g_1, \dots, g_{2d}$ (`List (StrongConv.Letter d)`) whose reduction $w(g_1, \dots, g_d) \in \mathbf F_d$ (`StrongConv.wordFree w`) is not the identity. Let $\pi(w) \in \{0, 1, 2, \dots\} \cup \{\infty\}$ be the primitivity rank of that reduction and $\mathrm{Crit}(w)$ its set of critical subgroups (`Puder.primitivityRank`, `Puder.Crit`), and let $b_s(w)$ (`StrongConv.wordCoeff w s`) be the coefficients of the expansion $N\,\mathbf E[\mathrm{tr}_N\, w(\boldsymbol S^N)] = \sum_s b_s(w)/N^s$. Then:
--   1. $b_s(w) = 0$ for every $s$ with $s + 2 \le \pi(w)$, that is, for $s \le \pi(w) - 2$ (for every $s$ when $\pi(w) = \infty$);
--   2. if $\pi(w) = r$ is finite, then $\mathrm{Crit}(w)$ is finite and $b_{r-1}(w) = |\mathrm{Crit}(w)|$ (with $r - 1$ read as $0$ when $r = 0$);
--   3. $|b_s(w)| \le q^{2(s+1)}$ for every $s \ge \pi(w)$;
--   4. $\pi(w) \le d$ or $\pi(w) = \infty$, that is, $\pi(w) \in \{0, \dots, d\} \cup \{\infty\}$.
--
--   The finiteness of $\mathrm{Crit}(w)$, which the paper's sentence presupposes when it writes $|\mathrm{Crit}(w)|$, is stated as a conjunct. Words may contain $g_0$ and need not be reduced, as in the paper's $\mathbf W_d$; such letters do not change $b_s(w)$ and only lengthen $q$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 26, the result of Puder cited in the proof of Lemma 8.5, which cites Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), §5.5 (proof of Proposition 5.1), with Theorem 2.3 (Puder–Parzanchevski)

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder

namespace Puder

theorem wordCoeff_eq_zero_and_eq_ncard_crit_and_abs_le (d : ℕ) (w : List (StrongConv.Letter d))
    (hw : StrongConv.wordFree w ≠ 1) :
    (∀ s : ℕ, (s : ℕ∞) + 2 ≤ primitivityRank (StrongConv.wordFree w) →
        StrongConv.wordCoeff w s = 0) ∧
      (∀ r : ℕ, primitivityRank (StrongConv.wordFree w) = r →
        (Crit (StrongConv.wordFree w)).Finite ∧
          StrongConv.wordCoeff w (r - 1) = (Crit (StrongConv.wordFree w)).ncard) ∧
      (∀ s : ℕ, primitivityRank (StrongConv.wordFree w) ≤ s →
        |StrongConv.wordCoeff w s| ≤ (w.length : ℝ) ^ (2 * (s + 1))) ∧
      (primitivityRank (StrongConv.wordFree w) ≤ d ∨
        primitivityRank (StrongConv.wordFree w) = ⊤) := by
  sorry

end Puder
