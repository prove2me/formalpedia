-- Prove2me | Theorems.Thm_SQMeanEstimation_lemma_3_16
-- name    : SQMeanEstimation.lemma_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:01.163931+00:00
-- url     : https://prove2.me/theorems/05efcdce-7b51-4827-89aa-cb2894ed1d84
-- title:
--   Lemma 3.16 — $\|z\|_q^q\le\|u^<\|_q^q+n^{-q/2}\|u^>\|_{q/2}^{q/2}$
-- statement:
--   Let $q\in(1,2)$ and $n>0$. Let $u\in[0,1]^d$, and let $v'\in\mathbb R^d$ be answers of $\mathrm{VSTAT}(n)$ to queries with means $u_i$, i.e.
--   $$
--   |v'_i-u_i|\le\max\Big\{\frac1n,\sqrt{\frac{u_i(1-u_i)}n}\Big\}\quad\text{for all }i .
--   $$
--   Let $v_i=v'_i\mathbf 1_{\{|v'_i|\ge2/n\}}$, $z=u-v$, $u^<_i=u_i\mathbf 1_{\{u_i<4/n\}}$ and $u^>_i=u_i\mathbf 1_{\{u_i\ge1/n\}}$. Then
--   $$
--   \sum_{i=1}^d|z_i|^q\le\sum_{i=1}^d|u^<_i|^q+n^{-q/2}\sum_{i=1}^d|u^>_i|^{q/2},
--   $$
--   that is, $\|z\|_q^q\le\|u^<\|_q^q+n^{-q/2}\|u^>\|_{q/2}^{q/2}$.
--
--   In the paper $u=2^j\,\mathbf E[R_j(w^+)]$; the lemma splits the error of the zeroed VSTAT estimate into a part from coordinates that were zeroed (which have small mean) and a part from coordinates that were kept (whose error the VSTAT variance bound controls).
--
--   Differences from the source:
--   - generalization: u = 2ʲ·w̄^{+,j} and v′ the VSTAT(n) answers to φᵢ(w) = 2ʲ(Rⱼ(w⁺))ᵢ → any u ∈ [0,1]ᵈ and any v′ with |v′ᵢ − uᵢ| ≤ max{1/n, √(uᵢ(1−uᵢ)/n)}; reason: the paper's u lies in [0,1]ᵈ (p.17: 2ʲ(Rⱼ(w⁺))ᵢ ∈ [0,1]) and its v′ satisfies the VSTAT guarantee (Definition 2.1), so the statement specializes to the source
--   - encoding: ‖z‖_q^q and ‖u^>‖_{q/2}^{q/2} → ∑ i, |z i| ^ q and ∑ i, |u^> i| ^ (q/2) (Real.rpow); reason: q/2 < 1, so ‖·‖_{q/2} is not a norm; the power of the expression is the sum itself
--   - encoding: VSTAT(n) with n an integer → n : ℝ with 0 < n; reason: the paper's n = (ε′/8)^{−p} is not an integer; every positive integer is a positive real
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, Lemma 3.16, p.17

import Mathlib
import Definitions.Def_SQMeanEstimation_vstatTol
import Definitions.Def_SQMeanEstimation_zeroSmall
import Definitions.Def_SQMeanEstimation_lowPart
import Definitions.Def_SQMeanEstimation_highPart

namespace SQMeanEstimation

/-- **Lemma 3.16 — error decomposition of the zeroed VSTAT estimate.**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, Lemma 3.16, p.17: "Let u ≐ 2ʲ · w̄^{+,j}, and
z ≐ u − v. Then ‖z‖_q^q ≤ ‖u^<‖_q^q + n^{−q/2} · ‖u^>‖_{q/2}^{q/2}, where u^<_i = uᵢ · 1_{uᵢ<4/n}
and u^>_i = uᵢ · 1_{uᵢ≥1/n} and for all i." Here (p.17) `v′ᵢ` is the answer of VSTAT(n) to a
query with mean `uᵢ ∈ [0, 1]`, and `vᵢ = v′ᵢ · 1_{|v′ᵢ|≥2/n}`.

Stated for any `u ∈ [0,1]ᵈ` and any answers `v′` with `|v′ᵢ − uᵢ| ≤ max{1/n, √(uᵢ(1−uᵢ)/n)}`.

**Formalization Note.** `‖z‖_q^q` is `Σ |zᵢ|^q` and `‖u^>‖_{q/2}^{q/2}` is `Σ |u^>ᵢ|^{q/2}`
(`q/2 < 1`, so this is not a norm). `v` is `zeroSmall n v'`, `u^<` is `lowPart n u`, `u^>` is
`highPart n u`. -/
theorem lemma_3_16 {d : ℕ} (q n : ℝ) (hq1 : 1 < q) (hq2 : q < 2) (hn : 0 < n)
    (u v' : Fin d → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1)
    (hv' : ∀ i, |v' i - u i| ≤ vstatTol n (u i)) :
    ∑ i, |u i - zeroSmall n v' i| ^ q ≤
      ∑ i, |lowPart n u i| ^ q + n ^ (-q / 2) * ∑ i, |highPart n u i| ^ (q / 2) := by sorry

end SQMeanEstimation
