-- Prove2me | Theorems.Thm_SQMeanEstimation_level_bound
-- name    : SQMeanEstimation.level_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:25.939128+00:00
-- url     : https://prove2.me/theorems/28a0fe09-64a5-4ed6-8dbd-eb821b54daf7
-- title:
--   Proof of Theorem 3.15 — level error $\|\bar w^{+,j}-2^{-j}v\|_q\le2^3n^{1/q-1}=\varepsilon'$
-- statement:
--   Let $q\in(1,2)$, $n>0$, $j\in\mathbb N$, let $u\in[0,1]^d$ with $\|u\|_1\le2^{(j+1)q-1}$ (eq. (2)), and let $v'$ be valid $\mathrm{VSTAT}(n)$ answers for means $u_i$: $|v'_i-u_i|\le\max\{1/n,\sqrt{u_i(1-u_i)/n}\}$. Let $v_i=v'_i\mathbf 1_{\{|v'_i|\ge2/n\}}$ and $z=u-v$, and let $u^<,u^>$ be as in Lemma 3.16. Then:
--
--   1. $\displaystyle\|z\|_q^q\le\|u^<\|_q^q+n^{-q/2}\|u^>\|_{q/2}^{q/2}\le n^{1-q}\big(2^{(j+3)q-3}+2^{(j+1)q-1}\big)\le n^{1-q}\,2^{(j+3)q}$;
--   2. for every $\bar w\in\mathbb R^d$ with $u=2^j\bar w$,
--   $$
--   \|\bar w-2^{-j}v\|_q=2^{-j}\|z\|_q\le2^3\,n^{1/q-1};
--   $$
--   3. for every $\varepsilon'>0$, if $n=(\varepsilon'/8)^{-p}$ with $p=q/(q-1)$, then $2^3n^{1/q-1}=\varepsilon'$.
--
--   So each level $j$ of the positive (and, symmetrically, negative) part is estimated to $\ell_q$ accuracy $\varepsilon'$ with $d$ queries to $\mathrm{VSTAT}((\varepsilon'/8)^{-p})$.
--
--   Differences from the source:
--   - generalization: u = 2ʲ·w̄^{+,j}, v′ the VSTAT(n) answers, w̄^{+,j} and n = (ε′/8)^{−p} fixed by the proof → any u ∈ [0,1]ᵈ with ∑ uᵢ ≤ 2^{(j+1)q−1}, any valid v′, any m̄ with u = 2ʲ·m̄, any n > 0; the identity 2³n^{1/q−1} = ε′ for every ε′ > 0 with n = (ε′/8)^{−q/(q−1)}; reason: the paper's objects satisfy these hypotheses (p.17, eq. (2), Definition 2.1), so the statement specializes to the source
--   - encoding: ‖·‖_q^q, ‖·‖_{q/2}^{q/2}; p → ∑ |·|^q, ∑ |·|^(q/2); p written as q/(q−1); reason: the definitions; p is the conjugate exponent of q (§2, p.10)
--   - encoding: VSTAT(n) with n an integer → n : ℝ with 0 < n; reason: the paper's n = (ε′/8)^{−p} is not an integer
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, proof of Theorem 3.15, p.18, displays after "Substituting eq. (3) and eq. (4) into Lemma 3.16"

import Mathlib
import Definitions.Def_SQMeanEstimation_lqNorm
import Definitions.Def_SQMeanEstimation_vstatTol
import Definitions.Def_SQMeanEstimation_zeroSmall
import Definitions.Def_SQMeanEstimation_lowPart
import Definitions.Def_SQMeanEstimation_highPart

namespace SQMeanEstimation

/-- **Error of one level of the estimate.**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, p.18: "Substituting eq. (3) and eq. (4) into
Lemma 3.16 we get ‖z‖_q^q ≤ ‖u^<‖_q^q + n^{−q/2} · ‖u^>‖_{q/2}^{q/2} ≤ n^{1−q} · (2^{(j+3)q−3} +
2^{(j+1)q−1}) ≤ n^{1−q} · 2^{(j+3)q}. Let w̃^{+,j} ≐ 2^{−j}v. We have ‖w̄^{+,j} − 2^{−j}v‖_q =
2^{−j} · ‖z‖_q ≤ 2³ · n^{1/q−1} = ε′." Here `n = (ε′/8)^{−p}`, `p = q/(q−1)` (p.17).

Hypotheses: `q ∈ (1,2)`, `n > 0`, `j ∈ ℕ`, `u ∈ [0,1]ᵈ` with `Σuᵢ ≤ 2^{(j+1)q−1}` (eq. (2)),
answers `v′` valid for VSTAT(n), `v = zeroSmall n v′`, `z = u − v`. Conclusions:
1. `Σ|zᵢ|^q ≤ Σ|u^<_i|^q + n^{−q/2}·Σ|u^>_i|^{q/2} ≤ n^{1−q}(2^{(j+3)q−3} + 2^{(j+1)q−1})
   ≤ n^{1−q}·2^{(j+3)q}`;
2. for every `m̄` with `u = 2ʲ·m̄`: `‖m̄ − 2^{−j}v‖_q = 2^{−j}‖z‖_q ≤ 2³·n^{1/q−1}`;
3. for every `ε′ > 0`, if `n = (ε′/8)^{−q/(q−1)}` then `2³·n^{1/q−1} = ε′`.

**Formalization Note.** `‖·‖_q^q` is `Σ |·|^q`; `‖·‖_q` is `lqNorm q`. -/
theorem level_bound {d : ℕ} (q n : ℝ) (hq1 : 1 < q) (hq2 : q < 2) (hn : 0 < n) (j : ℕ)
    (u v' : Fin d → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1)
    (hsum : ∑ i, u i ≤ (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1))
    (hv' : ∀ i, |v' i - u i| ≤ vstatTol n (u i)) :
    (∑ i, |u i - zeroSmall n v' i| ^ q ≤
        ∑ i, |lowPart n u i| ^ q + n ^ (-q / 2) * ∑ i, |highPart n u i| ^ (q / 2) ∧
      ∑ i, |lowPart n u i| ^ q + n ^ (-q / 2) * ∑ i, |highPart n u i| ^ (q / 2) ≤
        n ^ (1 - q) * ((2 : ℝ) ^ (((j : ℝ) + 3) * q - 3) + (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1)) ∧
      n ^ (1 - q) * ((2 : ℝ) ^ (((j : ℝ) + 3) * q - 3) + (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1)) ≤
        n ^ (1 - q) * (2 : ℝ) ^ (((j : ℝ) + 3) * q)) ∧
    (∀ mbar : Fin d → ℝ, u = (2 : ℝ) ^ j • mbar →
      lqNorm q (mbar - (2 : ℝ) ^ (-(j : ℤ)) • zeroSmall n v') =
          (2 : ℝ) ^ (-(j : ℤ)) * lqNorm q (u - zeroSmall n v') ∧
        (2 : ℝ) ^ (-(j : ℤ)) * lqNorm q (u - zeroSmall n v') ≤ 2 ^ 3 * n ^ (1 / q - 1)) ∧
    (∀ ε' : ℝ, 0 < ε' → n = (ε' / 8) ^ (-(q / (q - 1))) → 2 ^ 3 * n ^ (1 / q - 1) = ε')
    := by sorry

end SQMeanEstimation
