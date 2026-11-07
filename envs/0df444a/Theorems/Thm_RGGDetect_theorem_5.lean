-- Prove2me | Theorems.Thm_RGGDetect_theorem_5
-- name    : RGGDetect.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:27.349421+00:00
-- url     : https://prove2.me/theorems/3f67e4e6-c004-470f-be5e-d4ffc1d195d4
-- title:
--   Theorem 5 — posterior bounds $\mathrm{Post}(D_{\mathbf a})\le Cg_q(1+\Delta/p)$
-- statement:
--   For all sufficiently large constants $K$ and $M$ (depending on $\delta$) there is a constant $C=C(\delta,K,M)$ such that for every $D_{\mathbf a}$ in (17) of total degree $\|\mathbf a\|_1=2q$,
--
--   $$
--   \mathrm{Post}(D_{\mathbf a})\le C\,g_q\Big(1+\frac\Delta p\Big), \tag{22}
--   $$
--
--   for $\Delta$ as in (9) and $g_q$ as in (21).
--
--   This is the principal technical result: combined with Theorems 3 and 4 it gives $\Delta=o(1/n)$.
--
--   **Formalization Note** In the regime (1). Stated for every $K>2/\delta$, $M\ge K$ and slack $B^*\ge4M$; $C>0$ is chosen after $\delta,K,M,B^*$ and before the sequences. $D_{\mathbf a}$ is the explicit function (143) placed on the first $k$ vertices; the bound holds for all large $n$ and every $2\le k<K$, $1\le q\le M$, $\mathbf a\in\mathcal A_{k,q}$.
--
--   Differences from the source:
--   - generalization: the standing hypotheses (1) of Theorem 1, for all n → sequences in `Regime δ p d τ`: each hypothesis for all large n; reason: the statement is asymptotic, so sequences satisfying (1) for all n are covered
--   - generalization: for all sufficiently large K and M; B* suitably large → every K > 2/δ, M ≥ K and B* ≥ 4M; reason: these choices satisfy (67) (for 1 ≤ k < K, δ(3M+4−k) ≥ δ(2M+5) > 4 and δ(M+4) > 2), and the statement for all of them implies the printed 'for all sufficiently large' form
--   - encoding: D_a in (17) → the explicit D_a of (143) on the first k vertices; reason: Theorem 5 is not scale invariant, so D_a must be the paper's fixed function
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Theorem 5, eq. (22), p.8 (PDF p.10)

import Mathlib
import Definitions.Def_RGGDetect_Regime
import Definitions.Def_RGGDetect_Delta
import Definitions.Def_RGGDetect_Zsup
import Definitions.Def_RGGDetect_harmCoef

open Filter Topology

namespace RGGDetect

/-- **Theorem 5** (posterior bounds for spherical harmonics; arXiv:2610.08517, held version, sha256
e7bebd4a…, Theorem 5, p.8, eq. (22)): for all sufficiently large constants `K` and `M` (depending on
`δ`) there is a constant `C = C(δ, K, M)` such that for every `D_a` in (17) of total degree
`‖a‖₁ = 2q`, `Post(D_a) ≤ C g_q (1 + Δ/p)`, with `Δ` as in (9) and `g_q` as in (21).

**Formalization Note** In the regime (1). Stated for every `K > 2/δ`, `M ≥ K` and slack `B* ≥ 4M`
(these choices satisfy (67), so they are "sufficiently large"); `C` is chosen after `δ, K, M, B*` and
before the sequences. `D_a` is the fixed function (143) placed on the first `k` vertices; the bound is
for all large `n` and every `2 ≤ k < K`, `1 ≤ q ≤ M`, `a ∈ A_{k,q}`. -/
theorem theorem_5 (δ : ℝ) (hδ : 0 < δ) (K M B : ℕ) (hK : (K : ℝ) > 2 / δ) (hM : K ≤ M)
    (hB : 4 * M ≤ B) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : ℕ → ℝ) (d : ℕ → ℕ) (τ : ℕ → ℝ), Regime δ p d τ → ∀ᶠ n in atTop,
      ∀ k : ℕ, 2 ≤ k → k < K → ∀ q : ℕ, 1 ≤ q → q ≤ M → ∀ a ∈ Akq k q,
        Post (τ n) (onFirst (n := n) k (Da (d := d n) a)) ≤
          C * gT (d n) (τ n) q * (1 + Delta n (d n) (τ n) B / p n) := by sorry

end RGGDetect
