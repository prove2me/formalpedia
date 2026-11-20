-- Prove2me | Theorems.Thm_TightReleaseSchedules_Stationary_Supplement_exact_window_memory
-- name    : TightReleaseSchedules.Stationary.Supplement.exact_window_memory
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T04:23:29.056536+00:00
-- url     : https://prove2.me/theorems/9895e99a-e668-4d81-be92-f0bce21300b0
-- title:
--   Theorem B.1 — exact window memory, Θ(Wkb) persistent bits for exact gain queries
-- statement:
--   Let $W,k,b$ be positive integers. Stream rows are transformed pairs $(z_i,r_i)\in\mathbb R^k\times\mathbb R$. After $t\ge W$ arrivals the gain between $\omega,\omega'\in\mathbb R^k$ is
--
--   $$
--   G_t(\omega,\omega')=L_t(\omega)-L_t(\omega'),\qquad L_t(\omega)=\frac1{2W}\sum_{i=t-W+1}^{t}(r_i-z_i^\top\omega)^2 .
--   $$
--
--   Space is the number of persistent bits kept between arrivals.
--
--   1. **Upper bound.** Give each of the $k+1$ row coordinates (the $k$ coordinates of $z_i$ and the residual $r_i$) its own public alphabet of at most $2^b$ reals, and let every row coordinate lie in its alphabet. Some deterministic one-pass algorithm answers every gain query $G_t(\omega,\omega')$ exactly at every time $t\ge W$ on every stream. It occupies at most $2^{W(k+1)b+\lceil\log_2W\rceil+\lceil\log_2(W+1)\rceil}$ persistent states, that is, $W(k+1)b+O(\log W)$ bits.
--   2. **Deterministic lower bound.** Restrict to $w_0=0$ and coordinate projection: $r_i=0$, every coordinate of $z_i$ in $\{0,\dots,2^b-1\}$, and only the queries $G_t(0,e_j)$. Every deterministic algorithm that answers these queries exactly for every restricted stream and every $t\ge W$ occupies at least $2^{Wkb}$ persistent states, so it needs at least $Wkb$ bits.
--   3. **Randomized lower bound.** Consider a randomized algorithm with $M$ persistent bits, uncharged public randomness and fresh private randomness. Suppose that on every fixed restricted stream, at every $t\ge W$, its answer to every fixed query $G_t(0,e_j)$ is exactly correct with probability at least $2/3$. Then
--
--   $$
--   64M\ \ge\ Wkb\,\big(1-h_2(1/10)\big),
--   $$
--
--   where $h_2$ is the binary entropy in bits. Hence $M=\Omega(Wkb)$.
--   4. **Tightness.** Since $k\ge1$, $W(k+1)b+\lceil\log_2W\rceil+\lceil\log_2(W+1)\rceil\le4Wkb$, so exact persistent space is $\Theta(Wkb)$.
--
--   The theorem charges the expired-row history that a moment matrix cannot recover under deletions. This separates exact restricted-family memory $\Theta(Wkb)$ from ambient memory $\Theta(Wdb)$ (Corollary B.2).
--
--   **Formalization Note** The input is the stream of encoded transformed rows, as in Algorithm 3. The public $w_0$ and $U$ are read-only and uncharged, so they do not appear. Persistent space is the cardinality of the set of states reachable between arrivals. The explicit constants are those of the proof (an $O(\log W)$-bit ring pointer and fill count; $64M\ge N(1-h_2(1/10))$ with $N=Wkb$).
--
--   Differences from the source:
--   - encoding: examples $(x,y)\in\mathbb R^d\times\mathbb R$ with public affine family $w=w_0+U\omega$, rank-$k$ $U\in\mathbb R^{d\times k}$, $k\le d$, transformed to $z=U^\top x$, $r=y-w_0^\top x$ → the algorithm reads the transformed rows $(z_i,r_i)$ directly, with no $d$, $U$ or $w_0$; reason: Algorithm 3's input is the encoded transformed rows, and $w_0$, $U$ are read-only public data not charged as space.
--   - reading: "the transformed coordinates have specified $b$-bit encodings" → upper bound: every choice of public alphabets, one of at most $2^b$ reals for each of the $k+1$ row coordinates (a single shared alphabet is the special case of equal choices); lower bounds: $z$-coordinates in $\{0,\dots,2^b-1\}$ and $r_i=0$; reason: the lower-bound proof uses the alphabet $\{0,\dots,Q-1\}$ with $Q=2^b$ (p. 28). The reading "every $b$-bit alphabet" is false for the lower bound: with $b=1$ and alphabet $\{-1,1\}$, every restricted query has the constant value $G_t(0,e_j)=-1/2$, so zero bits suffice.
--   - reading: "$m$ persistent bits" → at most $2^m$ states reachable between arrivals (deterministic); an $m$-bit state string (randomized); reason: the space measure counts all persistent data-dependent bits between arrivals.
--   - reading: $O(W(k+1)b+\log W)$ and $\Omega(Wkb)$ → the explicit bounds $W(k+1)b+\lceil\log_2W\rceil+\lceil\log_2(W+1)\rceil$ and $64M\ge Wkb(1-h_2(1/10))$, and $\Theta(Wkb)$ as the explicit comparison $\le4Wkb$; reason: the constants are those of the proof (ring pointer and fill count capped at $W$, p. 28; $64M\ge N(1-h_2(1/10))$, p. 29).
--   - encoding: input streams and fresh randomness → infinite row sequences, a public seed from an arbitrary probability space, and independent private draws from an arbitrary probability space for the initial state, each transition and the query, with measurable maps; reason: a finite stream is a prefix of an infinite one and the answer at time $t$ depends only on the first $t$ rows; this is the model of §B.1.
-- source:
--   Jing Wang, When to Update a Pretrained Model: Tight Release Schedules under Distribution Shift, STOC 2027 submission #1096 (October 2026), Theorem B.1, printed p.28, PDF p.29; model §B.1 printed p.28, PDF p.29; proof printed pp.28–29, PDF pp.29–30

import Definitions.Def_TightReleaseSchedules_Stationary_Supplement_window_memory

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace TightReleaseSchedules.Stationary.Supplement

/-- Theorem B.1 (printed p. 28, PDF p. 29), with the `O(·)`/`Ω(·)` constants of its proof:
(1) for every choice of public per-coordinate alphabets of at most `2^b` reals each, a deterministic
one-pass algorithm answers every gain query exactly at every `t ≥ W` with at most
`2^{W(k+1)b + ⌈log₂ W⌉ + ⌈log₂(W+1)⌉}` persistent states; (2) every deterministic algorithm
exact on the restricted subclass (`w₀ = 0`, `r_i = 0`, coordinate projection, unsigned
`b`-bit coordinates, queries `(0, e_j)`) has at least `2^{Wkb}` persistent states; (3) every
randomized `M`-bit algorithm whose answer to each fixed restricted query on each fixed
restricted stream is exact with probability at least `2/3` has
`64M ≥ Wkb(1 − h₂(1/10))`; (4) for `k ≥ 1` the upper bound is at most `4Wkb`. -/
theorem exact_window_memory (W k b : ℕ) (hW : 0 < W) (hk : 0 < k) (hb : 0 < b) :
    (∀ A : Fin (k + 1) → Finset ℝ, (∀ c, (A c).card ≤ 2 ^ b) →
      ∃ alg : StreamAlgorithm k,
        (∀ x : ℕ → StreamRow k, (∀ n, RowInAlphabet (fun c => (A c : Set ℝ)) (x n)) →
          ∀ t, W ≤ t → ∀ ω ω' : Fin k → ℝ,
            alg.query (alg.stateAfter x t) ω ω' = windowGain W x t ω ω') ∧
        (alg.reachable (RowInAlphabet (fun c => (A c : Set ℝ)))).encard ≤
          (2 ^ (W * (k + 1) * b + Nat.clog 2 W + Nat.clog 2 (W + 1)) : ℕ)) ∧
    (∀ alg : StreamAlgorithm k,
      (∀ x : ℕ → StreamRow k, (∀ n, RestrictedRow b (x n)) →
        ∀ t, W ≤ t → ∀ j : Fin k,
          alg.query (alg.stateAfter x t) 0 (coordVec j) = windowGain W x t 0 (coordVec j)) →
      ((2 ^ (W * k * b) : ℕ) : ℕ∞) ≤ (alg.reachable (RestrictedRow b)).encard) ∧
    (∀ (M : ℕ) (alg : RandomizedStreamAlgorithm k M),
      (∀ x : ℕ → StreamRow k, (∀ n, RestrictedRow b (x n)) →
        ∀ t, W ≤ t → ∀ j : Fin k,
          (2 / 3 : ℝ≥0∞) ≤ alg.probAnswer x t 0 (coordVec j) (windowGain W x t 0 (coordVec j))) →
      ((W * k * b : ℕ) : ℝ) * (1 - Real.binEntropy (1 / 10) / Real.log 2) ≤ 64 * (M : ℝ)) ∧
    (W * (k + 1) * b + Nat.clog 2 W + Nat.clog 2 (W + 1) ≤ 4 * (W * k * b)) := by sorry

end TightReleaseSchedules.Stationary.Supplement
