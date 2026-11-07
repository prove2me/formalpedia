-- Prove2me | Theorems.Thm_SparseHistComm_eq_13_covering_upper_bound
-- name    : SparseHistComm.eq_13_covering_upper_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:41:39.766221+00:00
-- url     : https://prove2.me/theorems/e2c8f243-b47d-4cc2-b2a7-3889692d181f
-- title:
--   Eq. (13) — covering upper bound $C_{\mathrm{hom}}(D,\delta) \le \Lambda_{n,k,D}(\delta)\lceil\log d\rceil$
-- statement:
--   Let $n \ge 1$, $1 \le k \le d$, $d \ge 2$, $0 \le D < k$ and $0 \le \delta < 1$. Then
--   $$
--   C_{\mathrm{hom}}(D,\delta) \ \le\ \Lambda_{n,k,D}(\delta)\, \lceil \log d\rceil , \tag{13}
--   $$
--   with $\log$ in base 2. The randomized covering scheme with a (near-)minimizing policy of (12), in which each user draws its level from the common law $p_R$ and sends the $\lceil\log d\rceil$-bit indices of the kept active coordinates, is homogeneous, $(D,\delta)$-accurate, and has worst-case expected cost at most $n E_R[\sum_j j p_{R,j}]\lceil\log d\rceil$.
--
--   Differences from the source:
--   - encoding: protocols with any public randomness R, channels into {0,1}*, estimate from the messages and R → Protocol n d: Ω : Type with any probability measure, PMF (List Bool) channels and a decoder measurable in r, the decoder deterministic given (r, m); reason: every probability and expectation of the paper presupposes measurability in r; private server randomness can be moved into R; same protocols
--   - encoding: Λ_{n,k,D} as a min over (L(R), p_R) → Lambda: sInf over probability laws ν of p_R on stdSimplex ℝ (Fin (k+1)); reason: objective and constraint depend only on the law of p_R; the paper's Lemma 3 shows the minimum is attained, so the value agrees
--   - encoding: real inequality between nonnegative quantities → ENNReal.ofReal (real side) ≤ value in ℝ≥0∞; reason: the ℝ≥0∞ side is the paper's (possibly infinite) quantity; equivalent
--   - encoding: ⌈log d⌉ → Nat.clog 2 d; reason: equal for d ≥ 1
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section III, Eq. (13), p.7

import Mathlib
import Definitions.Def_SparseHistComm_Chom
import Definitions.Def_SparseHistComm_Lambda

namespace SparseHistComm

/-- **Eq. (13)** (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section III, p.7). The randomized covering scheme with a minimizing
policy gives the upper bound `C_hom(D, δ) ≤ Λ_{n,k,D}(δ)⌈log d⌉`.

**Formalization Note** `⌈log d⌉` is `Nat.clog 2 d`; the real right side is embedded by
`ENNReal.ofReal` (it is nonnegative). Since `Λ` is an infimum here, the bound holds for the
infimum (the paper's Lemma 3 shows it is attained; ε-optimal policies also suffice). -/
theorem eq_13_covering_upper_bound (n k d : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkd : k ≤ d) (hd : 2 ≤ d)
    (D δ : ℝ) (hD0 : 0 ≤ D) (hDk : D < k) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    Chom n k d D δ ≤ ENNReal.ofReal (Lambda n k D δ * (Nat.clog 2 d : ℝ)) := by sorry

end SparseHistComm
