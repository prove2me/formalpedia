-- Prove2me | Theorems.Thm_ReLUBinaryDepth_ProductTradeoff_Supplement_theorem_3_2
-- name    : ReLUBinaryDepth.ProductTradeoff.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:46:56.085482+00:00
-- url     : https://prove2.me/theorems/91c17e90-a909-4dba-bdcb-ae0abe46f578
-- title:
--   Theorem 3.2 — Boolean-output ReLU depth lower bounds imply threshold-circuit lower bounds
-- statement:
--   Let $f_n:\{0,1\}^n\to\{0,1\}$ for every $n$, and let $s:\mathbb N\to\mathbb R$ with $s(n)\ge 1$. Assume that for every polynomial $p(n)=c(n+1)^c$ ($c\in\mathbb N$), for all sufficiently large $n$, no strictly layered ReLU network with a ReLU output gate, of depth at most $s(n)$, width at most $p(n)$ and $p(n)$-bit rational weights Boolean-computes $f_n$. Then:
--
--   1. (Main claim.) There is no $c$ such that, for all sufficiently large $n$, $f_n$ is computed by a real-weighted threshold circuit of depth at most $s(n)/2$ and size at most $c(n+1)^c$.
--   2. If $s(n)\to\infty$, then $\{f_n\}\notin\mathrm{TC}^0$: there are no $d,c$ such that, for all sufficiently large $n$, $f_n$ is computed by a real-weighted threshold circuit of depth at most $d$ and size at most $c(n+1)^c$.
--   3. For every $d_0$, if $s(n)\ge 2d_0$ for all sufficiently large $n$, then $\{f_n\}\notin\mathrm{TC}^0_{d_0}$: there is no $c$ such that, for all sufficiently large $n$, $f_n$ is computed by a real-weighted threshold circuit of depth at most $d_0$ and size at most $c(n+1)^c$.
--
--   Thus any Boolean-output, bounded-precision analogue of the all-depth separation of Theorem 1.1 would give a lower bound against $\mathrm{TC}^0$, a long-standing open problem.
--
--   **Formalization Note** Circuit depth and network depth both count the output layer; the circuit size counts gates. Membership in $\mathrm{TC}^0$ is excluded even for families that only work for all sufficiently large $n$.
--
--   Differences from the source:
--   - generalization: {f_n} an explicit family → an arbitrary family f : (n : ℕ) → Cube n → Bool; reason: explicitness is never used in the proof; the statement for every family specializes to explicit ones
--   - reading: ReLU network of depth at most s(n), width at most poly(n), weights of at most poly(n) bits (Section 3) → strictly layered network of the published class with ReLU output gate, (depth : ℝ) ≤ s n, width ≤ c(n+1)^c, HasBitWeights (c(n+1)^c); reason: the narrowest network class the proof produces makes the non-existence hypothesis weakest and the theorem strongest
--   - reading: for all large n, f_n cannot be computed with poly(n) width and bits → ∀ c, ∀ᶠ n in atTop, no such network with width and bit-length ≤ c(n+1)^c; reason: the polynomial is fixed first and 'large n' may depend on it, the weakest reading of the hypothesis
--   - reading: not computed by threshold circuits of depth at most s(n)/2 and polynomial size; {f_n} ∉ TC0; {f_n} ∉ TC0_{d0} → ¬ ∃ c, ∀ᶠ n, ∃ real-weighted circuit with 2·depth ≤ s n (resp. depth ≤ d, depth ≤ d₀) and size ≤ c(n+1)^c computing f n; reason: real-weighted gates (as in the proof) and size counted in gates make the excluded class broadest; excluding families that work for all large n is at least as strong as excluding ones that work for every n
--   - encoding: s(n) = ω(1) → Tendsto s atTop atTop; reason: standard meaning of ω(1) for a real sequence
--   - encoding: s(n) ≥ 1, depth at most s(n)/2 → s : ℕ → ℝ with 1 ≤ s n; 2·(depth : ℝ) ≤ s n; reason: real-valued s as in the source; same instances
-- source:
--   Neil Krishnan, Elchanan Mossel, Depth Lower Bounds for ReLU Networks with Binary Inputs, STOC 2027 submission #1645 (October 2026), Theorem 3.2, PDF p. 7 = printed p. 7; proof pp. 7–8; definitions of B-bit weights, Boolean computation, TC⁰ and TC⁰_d, p. 6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1645.pdf (SHA-256 35accc05b120367e3d7a527b3b55383bc4a42c205bc78904f41eea6b2668555b)

import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Supplement_Layered
import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Supplement_ThresholdCircuit

namespace ReLUBinaryDepth.ProductTradeoff.Supplement

open ReLUBinaryDepth.ProductTradeoff Filter

/-- Theorem 3.2, PDF = printed p. 7. Hypothesis: for every polynomial `c·(n+1)^c`, for all large `n`,
no layered ReLU-output network of depth `≤ s n`, width and weight bit-length `≤ c·(n+1)^c`
Boolean-computes `f n`. Conclusions: the main claim, (1) and (2). -/
theorem theorem_3_2 (f : (n : ℕ) → Cube n → Bool) (s : ℕ → ℝ) (hs : ∀ n, 1 ≤ s n)
    (H : ∀ c : ℕ, ∀ᶠ n in atTop, ∀ N : Network n, IsLayered N → N.outputRelu = true →
      (N.depth : ℝ) ≤ s n → N.width ≤ c * (n + 1) ^ c →
      HasBitWeights (c * (n + 1) ^ c) N → ¬ BoolComputes N (f n)) :
    (¬ ∃ c : ℕ, ∀ᶠ n in atTop, ∃ C : RealThresholdCircuit n,
        2 * (C.depth : ℝ) ≤ s n ∧ C.size ≤ c * (n + 1) ^ c ∧ C.Computes (f n)) ∧
    (Tendsto s atTop atTop →
      ¬ ∃ d c : ℕ, ∀ᶠ n in atTop, ∃ C : RealThresholdCircuit n,
        C.depth ≤ d ∧ C.size ≤ c * (n + 1) ^ c ∧ C.Computes (f n)) ∧
    (∀ d₀ : ℕ, (∀ᶠ n in atTop, 2 * (d₀ : ℝ) ≤ s n) →
      ¬ ∃ c : ℕ, ∀ᶠ n in atTop, ∃ C : RealThresholdCircuit n,
        C.depth ≤ d₀ ∧ C.size ≤ c * (n + 1) ^ c ∧ C.Computes (f n)) := by sorry

end ReLUBinaryDepth.ProductTradeoff.Supplement
