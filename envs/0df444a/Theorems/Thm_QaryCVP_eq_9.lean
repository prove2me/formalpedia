-- Prove2me | Theorems.Thm_QaryCVP_eq_9
-- name    : QaryCVP.eq_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:00:16.001203+00:00
-- url     : https://prove2.me/theorems/d020188f-8129-4b21-86e4-3f992c39b33c
-- title:
--   Equation (9) — every execution runs in time $2^{T_{\rm in}n+o(n)}$ and space $2^{S_{\rm in}n+o(n)}$
-- statement:
--   Fix integers $k,\nu\ge1$, a real $\rho>0$, a rational $\eta>0$ and rational proportions $t_0,\dots,t_k$ satisfying the coordinate conditions, (3) and (5). With
--
--   $$T_{\rm in}=\max\Big\{\tfrac{h_k}{2},\max_{1\le i\le k}\big([h_i-d_i]_++[h_i-d_{i-1}]_+\big)\Big\},\qquad S_{\rm in}=\max\Big\{\tfrac{h_k}{2},\max_{0\le i<k}[h_i-d_i]_+,[h_k-d_{k-1}]_+\Big\},$$
--
--   there are programs $P$ (complete enumeration) and $S$ (first-output variant) such that:
--
--   1. on every input $(A,t)$ with $n,m\ge1$, $q\ge3$ and every coin tape, $P$ outputs a list of distinct vectors of $T$ solving $Ax=t$, and $S$ outputs the first vector of that list, or $\bot$ if it is empty;
--   2. for integers $q(n)\ge3$, $m(n)\ge1$ with $m\log q=\rho n+o(n)$, every execution of $P$ and of $S$ terminates in bit time $2^{T_{\rm in}n+o(n)}$ and bit space $2^{S_{\rm in}n+o(n)}$, up to a polynomial factor in the binary input length.
--
--   These exponents are the cost of the correction step in Corollaries 4.8 and 4.11.
--
--   Differences from the source:
--   - reading: the procedure (a specific algorithm of the paper) → there is a program of the RAM with every stated property, bundled for the same program; reason: decision 3: writing the algorithm as RAM code inside a statement is not feasible; the bundle carries every property later steps use
--   - reading: time and space in bit operations and bits, no machine named (p.13) → bit time and bit space of the published randomized log-cost rational RAM TwMSOCount.Main; reason: the paper's cost model; this machine charges bit operations at least as heavily (decision 1)
--   - reading: factors polynomial in the binary input length → (ℓ+1)^K with ℓ the total bit length of the input word and K fixed before the input; reason: p.13: poly is a polynomial in the binary input length
--   - reading: o(n) in the exponent → one g : ℕ → ℝ with g(n)/n → 0, fixed before the input; reason: p.13 asymptotic convention; one g for all clauses is the stronger form
--   - reading: on every input and execution → the run halts on every coin tape and the bounds hold on every tape; reason: p.13, Theorem 1.1
--   - reading: integers q ≥ 3 and m ≥ 1 depend on n with m log q = ρn + o(n) → for all sequences qs, ms with qs n ≥ 3, ms n ≥ 1 and (ms n · log₂ qs n − ρn)/n → 0; reason: the paper's 'Let n tend to infinity' with q, m depending on n; q is not fixed
--   - reading: the time and space of the procedure's executions under the section's parameter conditions → costs under the coordinate conditions, (3) and (5), for inputs with m log q = ρn + o(n); reason: the list sizes (7) use |G_i| = 2^{d_i n + o(n)}, which needs the rate assumption of §3.1
--   - generalization: the costs of the procedure → validity and the relation between the two output modes are clauses of the conclusion; reason: stated on pp.19–20 for the same procedure; specializes to (9)
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), §3.1.2, Eq. (9), p.24; output modes and validity, pp.19–20

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_encInst
import Definitions.Def_QaryCVP_ent3

open MeasureTheory Filter Topology TwMSOCount.Main
open scoped ENNReal

namespace QaryCVP

/-- **Equation (9)** (time and space of every execution of the representation procedure), for both
output modes. Kim, Kwon, Lee, Lee, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4),
§3.1.2, Eq. (9), p.24; output modes and validity, pp.19–20.

Fix integers `k, ν ≥ 1`, a real `ρ > 0`, a rational `η > 0` and rational proportions satisfying
the coordinate conditions, (3) and (5). There are programs `P` (complete enumeration) and `S`
(its first-output variant) such that:

1. on every input `(A, t)` (`n, m ≥ 1`, `q ≥ 3`) and coin tape, `P` outputs a list of distinct
   vectors of `T` solving `Ax = t`, and `S` outputs the first vector of that list, or `⊥` (the
   empty word) when the list is empty;
2. for integers `q(n) ≥ 3`, `m(n) ≥ 1` with `m log q = ρn + o(n)`, every execution of `P` and of `S`
   terminates in bit time `2^{T_in n + o(n)}` and bit space `2^{S_in n + o(n)}`, up to a polynomial
   factor in the binary input length, with
   `T_in = max{h_k/2, max_{1≤i≤k}([hᵢ − dᵢ]₊ + [hᵢ − dᵢ₋₁]₊)}`,
   `S_in = max{h_k/2, max_{0≤i<k}[hᵢ − dᵢ]₊, [h_k − d_{k−1}]₊}`.

**Formalization Note.** Decision 3 (existential form). The two output modes are the same execution
(p.19: "the variant that returns the first emitted vector …, and ⊥ if no vector is emitted"),
expressed by clause 1 on every tape. -/
theorem eq_9 (k ν : ℕ) (hk : 1 ≤ k) (hν : 1 ≤ ν) (ρ : ℝ) (hρ : 0 < ρ) (η : ℚ) (hη : 0 < η)
    (t : ℕ → ℚ) (hcoord : CoordCond k (fun i => (t i : ℝ)))
    (heq : EqCond k ρ η (fun i => (t i : ℝ))) :
    ∃ P S : Program,
      (∀ n m q : ℕ, 1 ≤ n → 1 ≤ m → 3 ≤ q →
        ∀ (A : Matrix (Fin m) (Fin n) (ZMod q)) (b : Fin m → ZMod q) (τ : ℕ → Bool),
          ∃ L : List (Fin n → ℤ),
            callOutput P (Config.init (encShort A b)) τ = some (L.map encZVec).flatten ∧
            L.Nodup ∧ (∀ x ∈ L, x ∈ ternarySet n (signCount0 k (t 0) n) ∧
              A.mulVec (fun j => (x j : ZMod q)) = b) ∧
            callOutput S (Config.init (encShort A b)) τ = some (optWord L.head?)) ∧
      (∀ qs ms : ℕ → ℕ, (∀ n, 3 ≤ qs n) → (∀ n, 1 ≤ ms n) → RateSeq ρ qs ms →
        ∃ (g : ℕ → ℝ) (K : ℕ), Tendsto (fun n => g n / n) atTop (𝓝 0) ∧
          ∀ n : ℕ, 1 ≤ n → ∀ (A : Matrix (Fin (ms n)) (Fin n) (ZMod (qs n)))
            (b : Fin (ms n) → ZMod (qs n)),
            RunsWithin P (encShort A b)
              ((2 : ℝ) ^ (Tin k ρ η (fun i => (t i : ℝ)) * n + g n) * polyF K (encShort A b))
              ((2 : ℝ) ^ (Sin k ρ η (fun i => (t i : ℝ)) * n + g n) * polyF K (encShort A b)) ∧
            RunsWithin S (encShort A b)
              ((2 : ℝ) ^ (Tin k ρ η (fun i => (t i : ℝ)) * n + g n) * polyF K (encShort A b))
              ((2 : ℝ) ^ (Sin k ρ η (fun i => (t i : ℝ)) * n + g n) * polyF K (encShort A b))) := by sorry

end QaryCVP
