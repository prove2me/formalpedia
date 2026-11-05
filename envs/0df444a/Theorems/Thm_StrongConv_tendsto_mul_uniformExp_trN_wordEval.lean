-- Prove2me | Theorems.Thm_StrongConv_tendsto_mul_uniformExp_trN_wordEval
-- name    : StrongConv.tendsto_mul_uniformExp_trN_wordEval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:43:48.293205+00:00
-- url     : https://prove2.me/theorems/58e1a019-3847-43cf-9b4d-8d1874c86f34
-- title:
--   Lemma 5.2 — first-order asymptotics of the expected trace of a word (Nica)
-- statement:
--   Let $w$ be a word in the letters $g_0 = e$, $g_i$, $g_{d+i} = g_i^{-1}$ whose reduction in $\mathbf F_d$ is not the identity, and write that reduction as $v^k$ with $v$ a non-power and $k \ge 1$. Then
--   $$\lim_{N\to\infty} N\,\mathbf E[\mathrm{tr}_N\, w(\boldsymbol S^N)] = \omega(k) - 1,$$
--   where $\omega(k)$ is the number of positive divisors of $k$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 20, Lemma 5.2, which applies Nica, A., On the number of cycles of given length of a free word in several random permutations, Random Structures Algorithms 5 (1994) 703–730, Corollary 1.3, https://doi.org/10.1002/rsa.3240050506

import Mathlib
import Definitions.Def_StrongConv

open Filter Topology

namespace StrongConv

theorem tendsto_mul_uniformExp_trN_wordEval (d : ℕ) (w : List (Letter d)) (hw : wordFree w ≠ 1)
    (v : FreeGroup (Fin d)) (k : ℕ) (hv : IsNonPower v) (hk : 1 ≤ k) (hwv : wordFree w = v ^ k) :
    Tendsto (fun N : ℕ => (N : ℝ) *
        uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (wordEval (sModel σ) w)))
      atTop (𝓝 ((k.divisors.card : ℝ) - 1)) := by
  sorry

end StrongConv
