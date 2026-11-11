-- Prove2me | Theorems.Thm_QaryCVP_corollary_4_8
-- name    : QaryCVP.corollary_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:59:49.305611+00:00
-- url     : https://prove2.me/theorems/13bd5b06-4601-4aff-b5e4-f9de3cce45a0
-- title:
--   Corollary 4.8 — Algorithm 3 at $\delta\le1$ in time $2^{\max\{1/4,T_{\rm in},e(a,c,\gamma)\}n+o(n)}$, with its $\gamma$-CVP guarantee
-- statement:
--   Fix rationals $\gamma>1$, $0<\beta<1/4$, $c>\beta$ with $h(\beta)>3/4$, a real $a>0$ satisfying (22), $\Theta_u(a)\le\Theta(a)e^{-au^2/\gamma^2}$ for $|u|\le1/2$, exponents $T_{\rm in},S_{\rm in}\ge0$ and $p\in(0,3/4]$. Let $S$ be a short-solver program (first-output mode) that on every input $(A,t)$ with $q\ge3$ and every coin tape returns $\bot$ or $v\in\{-1,0,1\}^{n_0}$ with $Av=t$, $\|v\|^2\le\beta n_0$, whose executions at equation rate $m\log q/n_0=1+o(1)$ take bit time $2^{T_{\rm in}n_0+o(n)}$ and bit space $2^{S_{\rm in}n_0+o(n)}$, and whose average success at that rate is at least $p$ for all but a $2^{-\Omega(n_0^{2/3})}$ fraction of matrices. Then there is a program $P$ (Algorithm 3 with these parameters) such that:
--
--   1. for every $q\ge2$, $n\ge1$, $m\ge0$ with $\delta\le1$, every input matrix, rational target and execution,
--
--   $$\text{time } 2^{\max\{1/4,\,T_{\rm in},\,e(a,c,\gamma)\}n+o(n)},\qquad\text{space } 2^{\max\{1/8,\,S_{\rm in},\,e(a,c,\gamma)/2\}n+o(n)},$$
--
--   up to a polynomial factor in the binary input length, with $e(a,c,\gamma)=(ac/\gamma^2+\ln\Theta(a))/(2\ln2)$;
--   2. for all sufficiently large $n$ and all $q\ge2$, $m$ with $\delta\le1$, all but a $2^{-\Omega(n^{2/3})}$ fraction of $H$ satisfy: with probability at least $1-2^{-\Omega(n)}$ over the coins, $P$ solves $\gamma$-CVP for every $y\in\mathbb Q^n$ simultaneously.
--
--   With the parameters of Appendix F.2 this gives the first row of Theorem 1.1.
--
--   **Formalization Note** The attempt constant $C$ and the exact subprocedures are internal to $P$.
--
--   Differences from the source:
--   - reading: the procedure (a specific algorithm of the paper) → there is a program of the RAM with every stated property, bundled for the same program; reason: decision 3: writing the algorithm as RAM code inside a statement is not feasible; the bundle carries every property later steps use
--   - reading: time and space in bit operations and bits, no machine named (p.13) → bit time and bit space of the published randomized log-cost rational RAM TwMSOCount.Main; reason: the paper's cost model; this machine charges bit operations at least as heavily (decision 1)
--   - reading: factors polynomial in the binary input length → (ℓ+1)^K with ℓ the total bit length of the input word and K fixed before the input; reason: p.13: poly is a polynomial in the binary input length
--   - reading: o(n) in the exponent → one g : ℕ → ℝ with g(n)/n → 0, fixed before the input; reason: p.13 asymptotic convention; one g for all clauses is the stronger form
--   - reading: on every input and execution → the run halts on every coin tape and the bounds hold on every tape; reason: p.13, Theorem 1.1
--   - reading: Algorithm 3 has time and space bounds … → there is a program P with these bounds that also carries the correctness guarantee of Theorem 4.7 at δ ≤ 1; reason: decision 3; without the correctness clause the existential cost statement would be satisfied by a trivial program
--   - generalization: S is the procedure of Corollary 3.3 with parameters satisfying §4.1 → S is any program with the stated validity, costs and average success; reason: the corollary uses only these properties; the paper's S satisfies them
--   - reading: exponents T_in, S_in per internal coordinate at equation rate 1 + o(1), uniformly; success at that rate → for every sequence (q(n₀), m(n₀)) with m log₂ q = n₀ + o(n₀): costs with one g and K, and success with c₀ > 0, N₀; reason: equivalent to uniform constants over rates 1 + o(1)
--   - reading: C > 0 a parameter of Algorithm 3 → C internal to the program P; reason: the correctness clause requires C as in Theorem 4.7
--   - reading: all but a 2^{−Ω(f(n))} fraction / probability 1 − 2^{−Ω(f(n))} → ∃ c > 0 and a threshold N with fraction (resp. probability) ≥ 1 − 2^{−c f(n)} for n ≥ N; reason: p.12 definition of Ω for sufficiently large n (R4)
--   - encoding: fraction of matrices → count of matrices with the property divided by q^{mn}, as a real number; reason: R5; same instances
--   - encoding: probability of an event of the coin tape → fair-coin measure of the event, with its measurability a clause of the conclusion; reason: the event is defined from a program run; measurability makes the probability meaningful
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Corollary 4.8, p.41; (11), p.33; (22) and (24), p.41; Theorem 4.7, p.39

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_matAvg
import Definitions.Def_QaryCVP_encInst
import Definitions.Def_QaryCVP_ent3

open MeasureTheory Filter Topology TwMSOCount.Main
open scoped ENNReal

namespace QaryCVP

/-- **Corollary 4.8** (uniform costs for density at most one), for Algorithm 3 together with its
correctness guarantee (Theorem 4.7) at `δ ≤ 1`. Kim, Kwon, Lee, Lee, STOC 2027 submission
manuscript (sha256 9aeb2ff4…ab4), Corollary 4.8, p.41; (11), p.33; (22) and (24), p.41;
Theorem 4.7, p.39.

Fix rationals `γ > 1`, `0 < β < 1/4`, `c > β` with `h(β) > 3/4`, a real `a > 0` satisfying (22),
`Θ_u(a) ≤ Θ(a)e^{−au²/γ²}` for `|u| ≤ 1/2`, and exponents `T_in, S_in ≥ 0`. Let `S` be a short-solver
program (first-output mode) that on every input `(A, t)` (`q ≥ 3`) and coin tape returns `⊥` or
`v ∈ {−1, 0, 1}^{n₀}` with `Av = t` and `‖v‖² ≤ βn₀`, whose executions at equation rate
`m log q / n₀ = 1 + o(1)` take bit time `2^{T_in n₀ + o(n)}` and bit space `2^{S_in n₀ + o(n)}`, and
whose average success at that rate is at least a fixed `p ∈ (0, 3/4]` for all but a
`2^{−Ω(n₀^{2/3})}` fraction of matrices. Then there is a program `P` (Algorithm 3 with these
parameters) such that

1. for every `q ≥ 2`, `n ≥ 1`, `m ≥ 0` with `δ ≤ 1`, every input matrix, rational target and
   execution, `P` runs in bit time `2^{max{1/4, T_in, e(a,c,γ)}n + o(n)}` and bit space
   `2^{max{1/8, S_in, e(a,c,γ)/2}n + o(n)}`, up to a polynomial factor in the binary input length,
   with `e(a, c, γ) = (ac/γ² + ln Θ(a))/(2 ln 2)`;
2. for all sufficiently large `n`, all `q ≥ 2`, `m` with `δ ≤ 1`, all but a `2^{−Ω(n^{2/3})}`
   fraction of `H` satisfy: with probability at least `1 − 2^{−Ω(n)}` over the coins, `P` solves
   γ-CVP for every `y ∈ Qⁿ` simultaneously.

**Formalization Note.** Decision 3: Algorithm 3 is abstracted to the existence of a program; the
correctness of Theorem 4.7 for the same algorithm is carried as clause 2 so that the cost clause
is not satisfied by a trivial program. The attempt constant `C` and the exact subprocedures are
internal to `P`. The rate hypotheses are stated for sequences `(q(n₀), m(n₀))` with
`m log₂ q = n₀ + o(n₀)` (R3, R4); `o(n)` is one `g` with `g(n)/n → 0`; `poly` is `(ℓ+1)^K`. -/
theorem corollary_4_8 (γ β c : ℚ) (a Ti Si p : ℝ) (hγ : 1 < γ) (hβ0 : 0 < β) (hβ1 : β < 1 / 4)
    (hcβ : β < c) (hhβ : 3 / 4 < binEnt β) (ha : 0 < a) (h22 : ThetaCond (1 / (γ : ℝ) ^ 2) a)
    (hTi : 0 ≤ Ti) (hSi : 0 ≤ Si) (hp0 : 0 < p) (hp1 : p ≤ 3 / 4) (S : Program)
    (hSvalid : ∀ n0 m q : ℕ, 1 ≤ n0 → 1 ≤ m → 3 ≤ q →
      ∀ (A : Matrix (Fin m) (Fin n0) (ZMod q)) (b : Fin m → ZMod q) (τ : ℕ → Bool),
        callOutput S (Config.init (encShort A b)) τ = some [] ∨
          ∃ v : Fin n0 → ℤ, callOutput S (Config.init (encShort A b)) τ = some (encZVec v) ∧
            (∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1) ∧ A.mulVec (fun j => (v j : ZMod q)) = b ∧
            sqNormZ v ≤ β * n0)
    (hScost : ∀ qs ms : ℕ → ℕ, (∀ n, 3 ≤ qs n) → (∀ n, 1 ≤ ms n) → RateSeq 1 qs ms →
      ∃ (g : ℕ → ℝ) (K : ℕ), Tendsto (fun n => g n / n) atTop (𝓝 0) ∧
        ∀ n0 : ℕ, 1 ≤ n0 → ∀ (A : Matrix (Fin (ms n0)) (Fin n0) (ZMod (qs n0)))
          (b : Fin (ms n0) → ZMod (qs n0)),
          RunsWithin S (encShort A b)
            ((2 : ℝ) ^ (Ti * n0 + g n0) * polyF K (encShort A b))
            ((2 : ℝ) ^ (Si * n0 + g n0) * polyF K (encShort A b)))
    (hSsucc : ∀ qs ms : ℕ → ℕ, (∀ n, 3 ≤ qs n) → (∀ n, 1 ≤ ms n) → RateSeq 1 qs ms →
      ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ N₀ : ℕ, ∀ n0 : ℕ, N₀ ≤ n0 →
        (∀ (A : Matrix (Fin (ms n0)) (Fin n0) (ZMod (qs n0))) b,
          MeasurableSet (firstSucc S A b)) ∧
        1 - (2 : ℝ) ^ (-c₀ * (n0 : ℝ) ^ ((2 : ℝ) / 3)) ≤
          matFrac (qs n0) (ms n0) n0 (fun A =>
            p ≤ vecAvg (qs n0) (ms n0) (fun b => (coinTape (firstSucc S A b)).toReal))) :
    ∃ (P : Program) (g : ℕ → ℝ) (K : ℕ), Tendsto (fun n => g n / n) atTop (𝓝 0) ∧
      (∀ n m q : ℕ, 1 ≤ n → 2 ≤ q → DensityLeOne q m n →
        ∀ (H : Matrix (Fin m) (Fin n) (ZMod q)) (y : Fin n → ℚ),
          RunsWithin P (encInst H y)
            ((2 : ℝ) ^ (max (max (1 / 4) Ti) (eCost a c γ) * n + g n) * polyF K (encInst H y))
            ((2 : ℝ) ^ (max (max (1 / 8) Si) (eCost a c γ / 2) * n + g n) *
              polyF K (encInst H y))) ∧
      (∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ N : ℕ, ∀ n m q : ℕ, N ≤ n → 2 ≤ q →
        DensityLeOne q m n →
        1 - (2 : ℝ) ^ (-c₁ * (n : ℝ) ^ ((2 : ℝ) / 3)) ≤
          matFrac q m n (fun H => GoodMatrix P γ H ((2 : ℝ) ^ (-c₂ * n)))) := by sorry

end QaryCVP
