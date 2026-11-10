-- Prove2me | Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_lemma_4_1
-- name    : RandOnlineSetCoverSqrt.LowerBound.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T19:35:59.900711+00:00
-- url     : https://prove2.me/theorems/fc0f8000-3879-4e86-b0c5-1861668c7c97
-- title:
--   Lemma 4.1 — adapted uniform-halving expectation bound
-- statement:
--   Let $C_0$ be an $(m,k,q,r)$-union-expanding family, so $1\le k\le r\le m$ and $q\ge2$. Set $T=4q$ and suppose $|C_0|=2^T$. Let $p$ be the joint law of random families $C^{(t)}$ and purchases $X_t$, for $0\le t\le T$, with $C^{(0)}=C_0$ and $X_0\subseteq\cdots\subseteq X_T\subseteq[m]$. For every $t<T$, conditional on the entire joint history through $X_t$, the next family is a uniformly chosen half of $C^{(t)}$. Thus purchases are made after the current family and before the next half is chosen.
--
--   Assume, on every positive-probability trajectory, that whenever $t<T$ and $|X_t|\le r$, some $W_t\in C^{(t)}$ satisfies $W_t\subseteq X_t$. Then
--
--   $$\mathbb E_p[|X_T|]\ge(1-e^{-q/4})r.$$
--
--   There is no assumption that purchases are a function only of the current family, and no independence assumption about witnesses or discard indicators. The constant $1/4$ and the strict expansion threshold are retained.
--
--   This is the expectation estimate for arbitrary adapted purchases under the source's full standing setup.
--
--   Differences from the source:
--   - encoding: subsets of [m] and nonnegative integer parameters → finite subsets of Fin m and natural-number parameters; reason: zero-based relabeling and nonnegativity in the type change no source instance
--   - encoding: arbitrary measurable finite-valued random trajectories with uniform next halves given history → their finite pushforward PMF and a joint-history event-mass identity, with assumptions on its support; reason: the finite joint law preserves every event and expectation; multiplication also handles null histories without a conditional-probability default
-- source:
--   Ilan Doron-Arad, Joseph (Seffi) Naor, STOC 2027 submission #1160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1160.pdf, Lemma 4.1 and preceding §4 setup, printed p. 10 / PDF p. 11; proof continues printed p. 11 / PDF p. 12

import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Halving

namespace RandOnlineSetCoverSqrt.LowerBound

/-- Lemma 4.1 with the complete §4 standing setup, printed p. 10 / PDF p. 11. -/
theorem lemma_4_1 {m k q r : ℕ} (C₀ : Family m)
    (hexpand : UnionExpanding k q r C₀) (hsize : C₀.card = 2 ^ (4 * q))
    (p : PMF (Trajectory m (4 * q))) (hprocess : HalvingProcess p C₀)
    (hwitness : ∀ z, p z ≠ 0 → ∀ t : Fin (4 * q),
      (z.2 t.castSucc).card ≤ r → ∃ W ∈ z.1 t.castSucc, W ⊆ z.2 t.castSucc) :
    (1 - Real.exp (-(q : ℝ) / 4)) * (r : ℝ) ≤ terminalExpectation p := by sorry

end RandOnlineSetCoverSqrt.LowerBound
