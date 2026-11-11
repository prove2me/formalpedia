-- Prove2me | Theorems.Thm_QaryCVP_corollary_3_3
-- name    : QaryCVP.corollary_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:59:51.640842+00:00
-- url     : https://prove2.me/theorems/0c15839f-6b65-443c-852e-6aefd81eb8f7
-- title:
--   Corollary 3.3 — the first-output variant succeeds with probability $\ge p$ for all but a $2^{-\Omega(n^{2/3})}$ fraction of $A$
-- statement:
--   Assume the hypotheses of Lemma 3.2 and additionally $h_0>\rho$. There is one randomized program $S$ (the first-output variant of the procedure) such that:
--
--   1. **Validity.** On every input $(A,t)$ with $n,m\ge1$, $q\ge3$ and every coin tape, $S$ halts and outputs either $\bot$ (the empty word) or one vector $x\in T$ with $Ax=t$.
--   2. **Costs (9).** As in Lemma 3.2, for $m\log q=\rho n+o(n)$: bit time $2^{T_{\rm in}n+o(n)}$ and bit space $2^{S_{\rm in}n+o(n)}$ times a polynomial in the input length.
--   3. **Average success.** For integers $q(n)\ge3$, $m(n)\ge1$ with $m\log q=\rho n+o(n)$ — all odd, or with (8) — and every fixed $p\in(0,1)$, there are $c>0$ and $N$ such that for $n\ge N$ all but a $2^{-cn^{2/3}}$ fraction of $A\in(\mathbb Z/q\mathbb Z)^{m\times n}$ satisfy
--
--   $$\Pr_{t,\omega}\big[S(A,t;\omega)\ne\bot\big]\ \ge\ p,$$
--
--   with $A$ fixed, $t$ uniform in $(\mathbb Z/q\mathbb Z)^m$ and $\omega$ the fair coins.
--
--   This is the average-success property the $\gamma$-CVP correction step needs.
--
--   Differences from the source:
--   - reading: the procedure (a specific algorithm of the paper) → there is a program of the RAM with every stated property, bundled for the same program; reason: decision 3: writing the algorithm as RAM code inside a statement is not feasible; the bundle carries every property later steps use
--   - reading: time and space in bit operations and bits, no machine named (p.13) → bit time and bit space of the published randomized log-cost rational RAM TwMSOCount.Main; reason: the paper's cost model; this machine charges bit operations at least as heavily (decision 1)
--   - reading: factors polynomial in the binary input length → (ℓ+1)^K with ℓ the total bit length of the input word and K fixed before the input; reason: p.13: poly is a polynomial in the binary input length
--   - reading: o(n) in the exponent → one g : ℕ → ℝ with g(n)/n → 0, fixed before the input; reason: p.13 asymptotic convention; one g for all clauses is the stronger form
--   - reading: on every input and execution → the run halts on every coin tape and the bounds hold on every tape; reason: p.13, Theorem 1.1
--   - reading: integers q ≥ 3 and m ≥ 1 depend on n with m log q = ρn + o(n) → for all sequences qs, ms with qs n ≥ 3, ms n ≥ 1 and (ms n · log₂ qs n − ρn)/n → 0; reason: the paper's 'Let n tend to infinity' with q, m depending on n; q is not fixed
--   - reading: if even moduli are allowed, also assume (8) → the success clause holds for every admissible sequence of odd moduli, and for every admissible sequence when (8) holds; reason: both cases of the sentence, for the same program
--   - reading: all but a 2^{−Ω(f(n))} fraction / probability 1 − 2^{−Ω(f(n))} → ∃ c > 0 and a threshold N with fraction (resp. probability) ≥ 1 − 2^{−c f(n)} for n ≥ N; reason: p.12 definition of Ω for sufficiently large n (R4)
--   - encoding: fraction of matrices → count of matrices with the property divided by q^{mn}, as a real number; reason: R5; same instances
--   - generalization: average success of the first-output variant → validity and costs (9) are clauses of the conclusion for the same program; reason: §3.1.1 and §3.1.2 state them for the same procedure; they specialize to the corollary
--   - encoding: probability of an event of the coin tape → fair-coin measure of the event, with its measurability a clause of the conclusion; reason: the event is defined from a program run; measurability makes the probability meaningful
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Corollary 3.3, p.22; validity §3.1.1, p.20; (9), p.24

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_matAvg
import Definitions.Def_QaryCVP_encInst
import Definitions.Def_QaryCVP_ent3

open MeasureTheory Filter Topology TwMSOCount.Main
open scoped ENNReal

namespace QaryCVP

/-- **Corollary 3.3** (average success of the first-output variant), with the validity of §3.1.1
and the costs (9) of the same procedure. Kim, Kwon, Lee, Lee, STOC 2027 submission manuscript
(sha256 9aeb2ff4…ab4), Corollary 3.3, p.22; validity §3.1.1, p.20; (9), p.24.

Under the hypotheses of Lemma 3.2 and additionally `h₀ > ρ`, there is one program `S` (the
first-output variant) with:

1. *validity*: on every input `(A, t)` (`n, m ≥ 1`, `q ≥ 3`) and every coin tape, `S` halts and
   outputs either `⊥` (the empty word) or one vector of `T` solving `Ax = t`;
2. *costs (9)*: as in Lemma 3.2, for `m log q = ρn + o(n)`;
3. *average success*: for integers `q(n) ≥ 3`, `m(n) ≥ 1` with `m log q = ρn + o(n)` — all odd, or
   with (8) — and every fixed `p ∈ (0, 1)`, there are `c > 0` and `N` such that for `n ≥ N` all but a
   `2^{−cn^{2/3}}` fraction of `A ∈ (Z/qZ)^{m×n}` satisfy `Pr_{t,ω}[S(A, t; ω) ≠ ⊥] ≥ p`, with `A`
   fixed, `t` uniform in `(Z/qZ)^m` and `ω` the fair coins.

**Formalization Note.** Decision 3 (existential form, bundled for the same program). `2^{−Ω(n^{2/3})}`
is `∃ c > 0, N` (R4); the fraction is a count over the `q^{mn}` matrices (R5). The success events
are measurable (clause of the conclusion). -/
theorem corollary_3_3 (k ν : ℕ) (hk : 1 ≤ k) (hν : 1 ≤ ν) (ρ : ℝ) (hρ : 0 < ρ) (η : ℚ)
    (hη : 0 < η) (t : ℕ → ℚ) (hcoord : CoordCond k (fun i => (t i : ℝ)))
    (heq : EqCond k ρ η (fun i => (t i : ℝ))) (hh0 : ρ < hRate (fun i => (t i : ℝ)) 0) :
    ∃ S : Program,
      (∀ n m q : ℕ, 1 ≤ n → 1 ≤ m → 3 ≤ q →
        ∀ (A : Matrix (Fin m) (Fin n) (ZMod q)) (b : Fin m → ZMod q) (τ : ℕ → Bool),
          callOutput S (Config.init (encShort A b)) τ = some [] ∨
            ∃ x : Fin n → ℤ, callOutput S (Config.init (encShort A b)) τ = some (encZVec x) ∧
              x ∈ ternarySet n (signCount0 k (t 0) n) ∧ A.mulVec (fun j => (x j : ZMod q)) = b) ∧
      (∀ qs ms : ℕ → ℕ, (∀ n, 3 ≤ qs n) → (∀ n, 1 ≤ ms n) → RateSeq ρ qs ms →
        ∃ (g : ℕ → ℝ) (K : ℕ), Tendsto (fun n => g n / n) atTop (𝓝 0) ∧
          ∀ n : ℕ, 1 ≤ n → ∀ (A : Matrix (Fin (ms n)) (Fin n) (ZMod (qs n)))
            (b : Fin (ms n) → ZMod (qs n)),
            RunsWithin S (encShort A b)
              ((2 : ℝ) ^ (Tin k ρ η (fun i => (t i : ℝ)) * n + g n) * polyF K (encShort A b))
              ((2 : ℝ) ^ (Sin k ρ η (fun i => (t i : ℝ)) * n + g n) * polyF K (encShort A b))) ∧
      (∀ qs ms : ℕ → ℕ, (∀ n, 3 ≤ qs n) → (∀ n, 1 ≤ ms n) → RateSeq ρ qs ms →
        ((∀ n, Odd (qs n)) ∨ ParityCond k ρ η (fun i => (t i : ℝ))) →
        ∀ p : ℝ, 0 < p → p < 1 →
          ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            (∀ (A : Matrix (Fin (ms n)) (Fin n) (ZMod (qs n))) b, MeasurableSet (firstSucc S A b)) ∧
            1 - (2 : ℝ) ^ (-c * (n : ℝ) ^ ((2 : ℝ) / 3)) ≤
              matFrac (qs n) (ms n) n (fun A =>
                p ≤ vecAvg (qs n) (ms n) (fun b => (coinTape (firstSucc S A b)).toReal))) := by sorry

end QaryCVP
