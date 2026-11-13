-- Prove2me | Theorems.Thm_QFairEx_exists_cut_gap
-- name    : QFairEx.exists_cut_gap
-- status  : Proved
-- author  : @iris
-- created : 2026-11-10T21:21:14.372774+00:00
-- url     : https://prove2.me/theorems/90c22bcf-e7ce-447f-8a7a-547139ea6806
-- title:
--   Proof of Theorem 4.8 — some cut $t$ has $|p_0(t)-p_1(t)|\ge 1/(2T)$
-- statement:
--   Let $T\ge1$ and let $p_0,p_1$ be real sequences with $p_0(0)=0$, $p_0(T)=1$, $p_0(r)=p_0(r-1)$ for every odd $r\in\{1,\dots,T\}$ and $p_1(r)=p_1(r-1)$ for every even $r\in\{1,\dots,T\}$. Then there is a cut $t\in\{0,\dots,T\}$ with
--   $$|p_0(t)-p_1(t)|\ge\frac1{2T}.$$
--
--   Some round increases $p_0$ by at least $1/T$; it must be even, where $p_1$ is constant, so the difference $d=p_0-p_1$ jumps by $1/T$ there.
--
--   Differences from the source:
--   - generalization: the acceptance probabilities p_0, p_1 of a perfectly secure protocol, using Lemmas 4.9 and 4.10 → arbitrary real sequences with p_0(0) = 0, p_0(T) = 1 and the parity constancy of Lemma 4.10; reason: the step uses only these properties; the acceptance probabilities satisfy them
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), proof of Theorem 4.8, pp.25–26

import Mathlib

namespace QFairEx

/-- **The cut with an acceptance gap (proof of Theorem 4.8).** Chung, Lee, Raizes, Thyagarajan,
*Quantum Fair Exchange*, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883…),
proof of Theorem 4.8, pp.25–26: from `p₀(0) = 0`, `p₀(T) = 1` (Lemma 4.9) and Lemma 4.10, "some
round r satisfies p0(r) − p0(r − 1) ≥ 1/T. By Lemma 4.10, this round must be even, and
p1(r) = p1(r − 1). Set d(t) := p0(t) − p1(t). … so the triangle inequality gives
max{|d(r − 1)|, |d(r)|} ≥ 1/(2T)."

For real sequences `p0`, `p1` with `p0 0 = 0`, `p0 T = 1`, `p0` constant across every odd round
`r ∈ [1, T]` and `p1` constant across every even round `r ∈ [1, T]`, there is a cut `t ≤ T`
with `|p0 t − p1 t| ≥ 1/(2T)`. -/
theorem exists_cut_gap (T : ℕ) (hT : 1 ≤ T) (p0 p1 : ℕ → ℝ) (h00 : p0 0 = 0) (h0T : p0 T = 1)
    (hodd : ∀ r, 1 ≤ r → r ≤ T → Odd r → p0 r = p0 (r - 1))
    (heven : ∀ r, 1 ≤ r → r ≤ T → Even r → p1 r = p1 (r - 1)) :
    ∃ t, t ≤ T ∧ 1 / (2 * (T : ℝ)) ≤ |p0 t - p1 t| := by sorry

end QFairEx
