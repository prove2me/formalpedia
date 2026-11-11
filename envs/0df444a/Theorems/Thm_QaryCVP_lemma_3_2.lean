-- Prove2me | Theorems.Thm_QaryCVP_lemma_3_2
-- name    : QaryCVP.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:59:53.030449+00:00
-- url     : https://prove2.me/theorems/3090f8e2-9b46-4cf0-ac25-21e8d0d118c6
-- title:
--   Lemma 3.2 — a fixed vector of $T$ is among the outputs with probability $1-2^{-(\nu-o(1))n^{2/3}}$
-- statement:
--   Fix integers $k,\nu\ge1$, a real constant $\rho>0$, and rational constants $\eta>0$ and $0<t_i<1/2$ ($0\le i\le k$) satisfying (3) and (5), with $h_i,r_i$ as in (4), $d_0=\rho$, $d_i=r_i-\eta$. There is one randomized program $P$ (the enumeration procedure of §3.1) such that:
--
--   1. **Validity.** On every input $(A,t)\in(\mathbb Z/q\mathbb Z)^{m\times n}\times(\mathbb Z/q\mathbb Z)^m$ with $n,m\ge1$, $q\ge3$ and every coin tape, $P$ halts and outputs a list of distinct vectors $x\in T$ (exactly $a_0=2^k\lfloor t_0n/2^k\rfloor$ entries of each nonzero sign) with $Ax=t$.
--   2. **Costs (9).** For integers $q=q(n)\ge3$, $m=m(n)\ge1$ with $m\log q=\rho n+o(n)$, every execution takes bit time $2^{T_{\rm in}n+o(n)}$ and bit space $2^{S_{\rm in}n+o(n)}$, up to a polynomial factor in the binary input length.
--   3. **Inclusion.** For such $q(n),m(n)$ — all odd, or with the even-modulus conditions (8) — there is $\varepsilon(n)\to0$ such that for all sufficiently large $n$ and every $x\in T$ fixed independently of a uniform $A$,
--
--   $$\Pr_{A,\omega}\big[x\text{ is among the outputs on input }(A,Ax)\big]\ \ge\ 1-2^{-(\nu-\varepsilon(n))n^{2/3}},$$
--
--   where $\omega$ are the fair coins.
--
--   This is the fixed-solution guarantee of the representation method; Corollary 3.3 averages it over $x$.
--
--   **Formalization Note** The output word of the enumeration is the concatenation of the emitted vectors. The "in particular" sentence of the lemma (failure at most $2^{-\nu' n^{2/3}}$ for every fixed $\nu'<\nu$) is equivalent to clause 3.
--
--   Differences from the source:
--   - reading: the procedure (a specific algorithm of the paper) → there is a program of the RAM with every stated property, bundled for the same program; reason: decision 3: writing the algorithm as RAM code inside a statement is not feasible; the bundle carries every property later steps use
--   - reading: time and space in bit operations and bits, no machine named (p.13) → bit time and bit space of the published randomized log-cost rational RAM TwMSOCount.Main; reason: the paper's cost model; this machine charges bit operations at least as heavily (decision 1)
--   - reading: factors polynomial in the binary input length → (ℓ+1)^K with ℓ the total bit length of the input word and K fixed before the input; reason: p.13: poly is a polynomial in the binary input length
--   - reading: o(n) in the exponent → one g : ℕ → ℝ with g(n)/n → 0, fixed before the input; reason: p.13 asymptotic convention; one g for all clauses is the stronger form
--   - reading: on every input and execution → the run halts on every coin tape and the bounds hold on every tape; reason: p.13, Theorem 1.1
--   - reading: integers q ≥ 3 and m ≥ 1 depend on n with m log q = ρn + o(n) → for all sequences qs, ms with qs n ≥ 3, ms n ≥ 1 and (ms n · log₂ qs n − ρn)/n → 0; reason: the paper's 'Let n tend to infinity' with q, m depending on n; q is not fixed
--   - reading: if even moduli are allowed, also assume (8) → the inclusion holds for every admissible sequence whose moduli are all odd, and for every admissible sequence when (8) holds; reason: both cases of the sentence, for the same program
--   - reading: Pr ≥ 1 − 2^{−(ν−o(1))n^{2/3}} for every fixed x ∈ T → one ε(n) → 0 serving every x ∈ T; reason: the proof's bound is uniform in x, and Corollary 3.3 averages over x
--   - generalization: validity and costs stated for the procedure → validity and costs are clauses of the conclusion for the same program; reason: §3.1.1 and §3.1.2 state them for the same procedure; they specialize to Lemma 3.2's inclusion claim
--   - encoding: probability of an event of the coin tape → fair-coin measure of the event, with its measurability a clause of the conclusion; reason: the event is defined from a program run; measurability makes the probability meaningful
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Lemma 3.2, p.20; validity §3.1.1, p.20; (9), p.24

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_matAvg
import Definitions.Def_QaryCVP_encInst
import Definitions.Def_QaryCVP_ent3

open MeasureTheory Filter Topology TwMSOCount.Main
open scoped ENNReal

namespace QaryCVP

/-- **Lemma 3.2** (fixed vector among the outputs), with the validity of §3.1.1 and the costs (9)
of the same procedure. Kim, Kwon, Lee, Lee, *Fast Provable Algorithms for Approximate CVP and
Exact SVP on Random q-ary Lattices*, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4),
Lemma 3.2, p.20; validity §3.1.1, p.20; (9), p.24.

Fix integers `k, ν ≥ 1`, a real `ρ > 0`, a rational `η > 0` and rational proportions
`t₀, …, t_k` satisfying the coordinate conditions and (3) and the equation conditions (5). There is
one program `P` of the log-cost RAM (the enumeration procedure, Algorithm 1 / Algorithm 7) with:

1. *validity*: on every input `(A, t)` with `n, m ≥ 1`, `q ≥ 3` and every coin tape, `P` halts and
   outputs a list of distinct vectors of `T = T₀` (exactly `a₀ = 2^k⌊t₀n/2^k⌋` entries of each
   sign) solving `Ax = t`;
2. *costs (9)*: for integers `q(n) ≥ 3`, `m(n) ≥ 1` with `m log q = ρn + o(n)`, every execution
   takes bit time `2^{T_in n + o(n)}` and bit space `2^{S_in n + o(n)}`, times a polynomial in the
   input length;
3. *inclusion*: for such `q(n), m(n)` — all odd, or with the even-modulus conditions (8) — there is
   `ε(n) → 0` such that for all large `n` and every `x ∈ T`, over a uniform `A` and the coins,
   `Pr[x is among the outputs on (A, Ax)] ≥ 1 − 2^{−(ν − ε(n)) n^{2/3}}`.

**Formalization Note.** Decision 3: the procedure is abstracted to the existence of a program with
these properties, bundled for the same program. The output word of the enumeration is the
concatenation of the emitted vectors (each of length `n ≥ 1`). "If even moduli are allowed, also
assume (8)" is the disjunction in clause 3. The `o(1)` is uniform over `x ∈ T` (the proof's
bound, used by Corollary 3.3's averaging). -/
theorem lemma_3_2 (k ν : ℕ) (hk : 1 ≤ k) (hν : 1 ≤ ν) (ρ : ℝ) (hρ : 0 < ρ) (η : ℚ) (hη : 0 < η)
    (t : ℕ → ℚ) (hcoord : CoordCond k (fun i => (t i : ℝ)))
    (heq : EqCond k ρ η (fun i => (t i : ℝ))) :
    ∃ P : Program,
      (∀ n m q : ℕ, 1 ≤ n → 1 ≤ m → 3 ≤ q →
        ∀ (A : Matrix (Fin m) (Fin n) (ZMod q)) (b : Fin m → ZMod q) (τ : ℕ → Bool),
          ∃ L : List (Fin n → ℤ),
            callOutput P (Config.init (encShort A b)) τ = some (L.map encZVec).flatten ∧
            L.Nodup ∧ ∀ x ∈ L, x ∈ ternarySet n (signCount0 k (t 0) n) ∧
              A.mulVec (fun j => (x j : ZMod q)) = b) ∧
      (∀ qs ms : ℕ → ℕ, (∀ n, 3 ≤ qs n) → (∀ n, 1 ≤ ms n) → RateSeq ρ qs ms →
        ∃ (g : ℕ → ℝ) (K : ℕ), Tendsto (fun n => g n / n) atTop (𝓝 0) ∧
          ∀ n : ℕ, 1 ≤ n → ∀ (A : Matrix (Fin (ms n)) (Fin n) (ZMod (qs n)))
            (b : Fin (ms n) → ZMod (qs n)),
            RunsWithin P (encShort A b)
              ((2 : ℝ) ^ (Tin k ρ η (fun i => (t i : ℝ)) * n + g n) * polyF K (encShort A b))
              ((2 : ℝ) ^ (Sin k ρ η (fun i => (t i : ℝ)) * n + g n) * polyF K (encShort A b))) ∧
      (∀ qs ms : ℕ → ℕ, (∀ n, 3 ≤ qs n) → (∀ n, 1 ≤ ms n) → RateSeq ρ qs ms →
        ((∀ n, Odd (qs n)) ∨ ParityCond k ρ η (fun i => (t i : ℝ))) →
        ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
          ∀ᶠ n in atTop, ∀ x ∈ ternarySet n (signCount0 k (t 0) n),
            let E := fun (A : Matrix (Fin (ms n)) (Fin n) (ZMod (qs n))) =>
              {τ : ℕ → Bool | ∃ L : List (Fin n → ℤ),
                callOutput P (Config.init (encShort A (A.mulVec (fun j => (x j : ZMod (qs n))))))
                  τ = some (L.map encZVec).flatten ∧ x ∈ L}
            (∀ A, MeasurableSet (E A)) ∧
              1 - (2 : ℝ) ^ (-((ν : ℝ) - ε n) * (n : ℝ) ^ ((2 : ℝ) / 3)) ≤
                matAvg (qs n) (ms n) n (fun A => (coinTape (E A)).toReal)) := by sorry

end QaryCVP
