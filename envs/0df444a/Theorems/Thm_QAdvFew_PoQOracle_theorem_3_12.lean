-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_theorem_3_12
-- name    : QAdvFew.PoQOracle.theorem_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:52:22.634133+00:00
-- url     : https://prove2.me/theorems/cb64660e-a9cc-4f05-b6dc-718f85539488
-- title:
--   Theorem 3.12 — direct product theorem for circuits
-- statement:
--   There is a universal constant $c>0$ such that the following holds. Let $\delta\in(0,1)$, let $f:\{0,1\}^n\to\{0,1\}$ be any Boolean function, let $\mathrm{Samp}$ be any distribution on $\{0,1\}^n$, and let $\mathcal A$ be an algorithm with
--   $$\Pr_{\mathrm{Samp}\to x_1,\dots,x_t}[\mathcal A(x_1,\dots,x_t)=(f(x_1),\dots,f(x_t))]\ge e^{-c\delta t}.$$
--   Then there is an $\mathsf{AC}^0$ circuit $C$ with oracle gates, of size $\mathrm{poly}(n,t,\log(1/\delta),e^{c\delta t})$, with
--   $$\Pr_{\mathrm{Samp}\to x}[C^{\mathcal A}(x)=f(x)]\ge1-\delta.$$
--
--   This is Theorem 1.2 of [IJKW10]; it turns a weak solver of many instances into a strong solver of one.
--
--   Differences from the source:
--   - reading: AC0, poly(·) → one universal depth bound k and one bound k(n+t+log₂(1/δ)+e^{cδt})^k; reason: the uniform reading of asymptotic notation: constants come after the fixed parameters and before the quantified objects
--   - reading: any algorithm A → a deterministic function; reason: both probabilities are over Samp only (the subscripts), so A has no coins of its own; this is the form the paper applies (proof of Lemma 4.11: "Fix the randomness of C′")
--   - encoding: x_1, …, x_t → t ≥ 1; reason: the tuple has at least one entry; at t = 0 the hypothesis is empty and the conclusion would be false for a hard f
--   - encoding: oracle gates calling A → one gate per output bit of A (dpOracle); reason: an oracle gate returns one bit
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Theorem 3.12, p. 15 (PDF p. 17)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Circuit
import Definitions.Def_QAdvFew_PoQOracle_dpOracle

namespace QAdvFew.PoQOracle

open Classical in
/-- **Theorem 3.12 (Direct product theorem for circuits, Theorem 1.2 of [IJKW10])** (Goldin,
Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1,
Theorem 3.12, p. 15 (PDF p. 17)). There is a universal constant `c > 0` such that: for
`δ ∈ (0, 1)`, any `f : {0,1}^n → {0,1}`, any distribution `Samp` on `{0,1}^n` and any algorithm `A`
with `Pr_{x₁,…,x_t←Samp}[A(x₁, …, x_t) = (f(x₁), …, f(x_t))] ≥ e^{−cδt}`, there is an `AC0` circuit
`C` with oracle gates of size `poly(n, t, log(1/δ), e^{cδt})` with `Pr_{x←Samp}[C^A(x) = f(x)] ≥ 1 − δ`.

**Formalization Note** "`AC0`" and "`poly`" are universal: one depth bound `k` and one polynomial
`k (n + t + log₂(1/δ) + e^{cδt})^k`. `A` is a deterministic function (both
probabilities are over `Samp` only, as their subscripts say; the proof of Lemma 4.11 fixes the
randomness first). `x₁, …, x_t` are independent samples. `C` has AND, OR, NOT and
oracle gates, its oracle gates asking `A` for one output bit (`dpOracle`). `t ≥ 1` (the source's
`x₁, …, x_t`). -/
theorem theorem_3_12 : ∃ c : ℝ, 0 < c ∧ ∃ k : ℕ, ∀ (n t : ℕ), 1 ≤ t → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ (f : (Fin n → Bool) → Bool) (Samp : PMF (Fin n → Bool))
      (A : (Fin t → Fin n → Bool) → (Fin t → Bool)),
      Real.exp (-(c * δ * t)) ≤
          ∑ xs : Fin t → Fin n → Bool, (∏ i, (Samp (xs i)).toReal) *
            (if A xs = fun i => f (xs i) then 1 else 0) →
      ∃ C : Circuit (Fin n), C.NoXor ∧ C.depth ≤ k ∧
        (C.size : ℝ) ≤ k * (n + t + Real.logb 2 (1 / δ) + Real.exp (c * δ * t)) ^ k ∧
        1 - δ ≤ ∑ x : Fin n → Bool, (Samp x).toReal *
          (if C.eval1 (dpOracle n t A) x = f x then 1 else 0) := by sorry

end QAdvFew.PoQOracle
