-- Prove2me | Theorems.Thm_QuarticGap_Supplement_theorem_3_9
-- name    : QuarticGap.Supplement.theorem_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:53:43.272601+00:00
-- url     : https://prove2.me/theorems/29a174bb-5783-416e-95ec-8bb83129cf46
-- title:
--   Theorem 3.9 — Fourier sampling on $K \ge 128$ characters needs more than $\lfloor M/(32\log(512K))\rfloor$ classical queries
-- statement:
--   Let $S \subseteq \{0,1\}^m$ be a set of $K = |S| \ge 128$ characters, $M = 2^m$, and
--   $$
--   q_0 = \Bigl\lfloor \frac{M}{32\log(512K)} \Bigr\rfloor .
--   $$
--   Then:
--
--   1. every classical algorithm that makes at most $q_0$ queries to $f$ on every Boolean function $f$ has, for some Boolean function $f$, an output distribution at total variation distance at least $31/1536$ from $p_{z_f}$;
--   2. in particular, every classical algorithm that solves $\mathrm{Samp}_S(1/100)$, that is, samples within total variation distance $1/100$ of $p_{z_f}$ for every $f$, makes more than $q_0$ queries on some $f$.
--
--   Here $z_f = (Z_s(f)/\sqrt K)_{s\in S}$ followed by the coordinate $z_f(\bot) = 1$. For $K = \sqrt M$ the bound is $\Omega(M/\log M)$ while $O(M^{1/4})$ quantum queries suffice (Theorem 3.10), the same quartic gap as for the linear systems of the main theorem.
--
--   **Formalization Note** A query is a point $\sigma$ and returns $f(\sigma)$; outputs are in `Option S` with `none` $= \bot$; inputs are all Boolean functions, with no promise.
--
--   Differences from the source:
--   - reading: a randomized classical algorithm → QueryAlg, a behaviour strategy on transcripts with unrestricted computation; reason: an algorithm with private coins and perfect recall has a behaviour strategy with the same law (Kuhn); the input reaches it only through the answers
--   - encoding: output distribution within total variation distance ε → sampleErr, which counts the mass of non-halting runs as an extra outcome; reason: it is TV for an algorithm that halts almost surely and gives a non-halting algorithm no advantage
--   - encoding: outcomes S ∪ {⊥} → Option S with none = ⊥; reason: the same finite set
--   - encoding: the standing assumption m ≥ 2 of §3.1 → not a binder; reason: K ≥ 128 and K ≤ 2^m imply m ≥ 7
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Theorem 3.9, p.27

import Mathlib
import Definitions.Def_QuarticGap_Supplement_fourierZ

open QAlgorithms

namespace QuarticGap.Supplement

/-- Theorem 3.9 (Chakrabarti, Herman, Kim, Ozgul, *The Quartic Gap Between Quantum and Dequantized
Algorithms for Linear Algebra Is Tight*, arXiv:2610.42069 (file sha256 9f68aaf9…), p.27). Let
`K = |S| ≥ 128` and `q₀ = ⌊M/(32 log(512K))⌋`. Every classical algorithm that makes at most `q₀`
queries on every input has, for some Boolean function `f`, an output distribution at total variation
distance at least `31/1536` from `p_{z_f}`. In particular, `Samp_S(1/100)` requires more than `q₀`
queries.

**Formalization Note** A classical algorithm is a `QueryAlg` that queries `f` directly (§2.5, p.18):
a query is a point `σ ∈ {0,1}^m` and the answer is `f(σ)`; it outputs an element of `S ∪ {⊥}`
(`Option S`). Inputs are all Boolean functions, with no promise. "Makes at most `q₀` queries" is over
all runs. The error `sampleErr` is the total variation distance of the output law, the mass of
non-halting runs counted as an extra outcome. The section's standing `m ≥ 2` is implied by
`K ≥ 128`, since `K ≤ 2^m`. -/
theorem theorem_3_9 (m : ℕ) (S : Finset (Qubits m)) (hK : 128 ≤ S.card) :
    (∀ alg : QueryAlg (Qubits m) ℤˣ (Option S),
      (∀ f : Qubits m → ℤˣ, alg.MakesAtMost (directRespond f) (q0S S)) →
      ∃ f : Qubits m → ℤˣ, (31 / 1536 : ℝ) ≤ alg.sampleErr (directRespond f) (fourierTarget S f)) ∧
    (∀ alg : QueryAlg (Qubits m) ℤˣ (Option S),
      (∀ f : Qubits m → ℤˣ, alg.sampleErr (directRespond f) (fourierTarget S f) ≤ 1 / 100) →
      ∃ f : Qubits m → ℤˣ, ¬ alg.MakesAtMost (directRespond f) (q0S S)) := by sorry

end QuarticGap.Supplement
