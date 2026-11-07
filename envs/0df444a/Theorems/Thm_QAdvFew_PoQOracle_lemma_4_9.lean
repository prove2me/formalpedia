-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_lemma_4_9
-- name    : QAdvFew.PoQOracle.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:30.307028+00:00
-- url     : https://prove2.me/theorems/6950efe6-d5b2-4937-89dc-b7e3a49b3798
-- title:
--   Lemma 4.9 — the Forrelated oracle is useless to classical algorithms
-- statement:
--   Let $p,q,s$ be polynomials, let $f^A_n:\{0,1\}^{s(n)}\to\{0,1\}^{q(n)}$ be any family of functions depending only on the $A$ portion of the oracle, let $\mathrm{Samp}^A(1^n)$ be any distribution on $\{0,1\}^{s(n)}$ depending only on the $A$ portion, and let $M^O$ be an oracle Turing machine running in time $p(|x|)$. Then
--   $$\Bigl|\Pr_{O\leftarrow\mathcal D,\ x\leftarrow\mathrm{Samp}^A(1^n)}[M^O(x)=f^A_n(x)]-\Pr_{O\leftarrow\mathcal D^{(n)},\ x\leftarrow\mathrm{Samp}^A(1^n)}[M^O(x)=f^A_n(x)]\Bigr|\le2^{-\Omega(n^2)},$$
--   where $\mathcal D^{(n)}$ replaces $B_t$ for $t\ge n$ with truly random functions.
--
--   So, for a classical algorithm, the Forrelation structure at high levels can be replaced by uniform randomness.
--
--   Differences from the source:
--   - generalization: the oracle distribution D built from the Forrelation distribution of [RT19] → D built from any family F with the properties of Lemma 3.10 used; reason: the construction of [RT19] is one such family by Lemma 3.10, and the paper's proof uses only these properties
--   - reading: 2^{−Ω(n²)} → ∃ c > 0 and n₀ depending only on p, q, s, with the bound for all n ≥ n₀ and all M, f, Samp; reason: constants are fixed before the quantified objects; this is the strongest form, since the paper's proof may let n₀ depend on the machine
--   - generalization: M running in time p(|x|) → every machine, with its output read after p(s(n)) steps; reason: a machine running in time p is its own clocked version
--   - encoding: functions and distributions dependent only on the A portion → measurable functions of the oracle A; reason: the printed probabilities are defined only for measurable dependence
--   - reading: machines of S_t syntactically restricted to query levels up to ⌊√t⌋ and to the time and space bounds → every pair of code length below t, run with the truncated oracle and clocks; reason: makes the recursion well-founded; same value on machines obeying the restrictions
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Lemma 4.9, p. 24 (PDF p. 26)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_agreeProb
import Definitions.Def_QAdvFew_PoQOracle_ForrAC0

open MeasureTheory

namespace QAdvFew.PoQOracle

/-- **Lemma 4.9 (Forrelated oracle is useless to classical algorithms)** (Goldin, Lombardi, Morimae,
*Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Lemma 4.9, p. 24
(PDF p. 26)). Let `p, q, s` be polynomials, `f^A_n : {0,1}^{s(n)} → {0,1}^{q(n)}` functions and
`Samp^A(1^n)` distributions on `{0,1}^{s(n)}` depending only on the `A` part of the oracle, and `M^O`
an oracle Turing machine running in time `p(|x|)`. Then
`|Pr_{O←D, x←Samp^A(1^n)}[M^O(x) = f^A_n(x)] − Pr_{O←D^(n), x←Samp^A(1^n)}[M^O(x) = f^A_n(x)]|
≤ 2^{−Ω(n²)}`.

**Formalization Note** `D` is built from any family `F` with property (2) of Lemma 3.10. The
`2^{−Ω(n²)}` is uniform: `c > 0` and `n₀` depend only on `p, q, s`, not on `M`, `f` or `Samp`.
`M^O(x)` is the output of `M` after `p(|x|)` steps (a machine running in time `p` is its own clocked
version). `f` and `Samp` are functions of the oracle `A`, measurable so that the probabilities are
integrals of measurable functions. -/
theorem lemma_4_9 (F : (N : ℕ) → PMF (Fin N → Bool)) (hF : ForrAC0 F)
    (p q s : Polynomial ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ (M : OTM) (n : ℕ), n₀ ≤ n →
      ∀ (f : Oracle → (Fin (s.eval n) → Bool) → (Fin (q.eval n) → Bool))
        (Samp : Oracle → PMF (Fin (s.eval n) → Bool)),
        Measurable f → (∀ x, Measurable fun A => Samp A x) →
        |(agreeProb F ⊤ (s.eval n) (q.eval n) f Samp M (p.eval (s.eval n))).toReal -
            (agreeProb F (n : ℕ∞) (s.eval n) (q.eval n) f Samp M (p.eval (s.eval n))).toReal| ≤
          (2 : ℝ) ^ (-(c * (n : ℝ) ^ 2)) := by sorry

end QAdvFew.PoQOracle
