-- Prove2me | Theorems.Thm_SetMultCost_theorem_1_2
-- name    : SetMultCost.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:08.431694+00:00
-- url     : https://prove2.me/theorems/cc695c69-3d2c-4509-82ca-536900829dcd
-- title:
--   Theorem 1.2 — product-depth $\Delta$ circuits for $\mathrm{IMM}_{n,d}$ need size $\exp(\Omega(d^{1/(F(\Delta+1)-1)}/p^2)\log n)$ in characteristic $p$
-- statement:
--   Let $F(0)=F(1)=1,F(2)=2,\dots$ be the Fibonacci numbers and $R(\Delta)=F(\Delta+1)-1$.
--
--   1. $\mathrm{IMM}_{n,d}$ is a nonzero set-multilinear polynomial, homogeneous of degree $d$, for all $n,d\ge1$.
--   2. $\mathrm{IMM}_{n,d}$ is in VP: there is $K$ such that over every field and for all $n,d\ge1$ it has a circuit of size at most $K(nd)^K$.
--   3. For all $\Delta\ge1$ and $C>0$ there are $c>0$ and $n_0$ such that, for every field $F$ of prime characteristic $p$, every $n\ge n_0$ and every $2\le d\le C\log n/\log\log n$, every circuit computing $\mathrm{IMM}_{n,d}$ with product-depth at most $\Delta$ has size at least
--
--   $$\exp\Big(c\,\frac{d^{1/R(\Delta)}}{p^2}\,\log n\Big).$$
--
--   The circuits in clause 3 are arbitrary directed acyclic graphs with unbounded fan-in, computing $\mathrm{IMM}_{n,d}$ as a polynomial; they are not assumed homogeneous or set-multilinear. Over characteristic $0$ such a bound is false at $\Delta=2$, by depth reduction to non-homogeneous depth-four circuits of size $n^{O(d^{1/3})}$.
--
--   Differences from the source:
--   - generalization: "There exists a set-multilinear polynomial P(x) in VP" → P = IMM_{n,d}, named; reason: the proof reaches IMM_{n,d} by projection (Corollary 2.7), and the named polynomial gives the existential for d ≥ 2
--   - generalization: alternately layered circuits of product-depth Δ → any DAG with a height function bounded by Δ; reason: contains the layered class; layering costs only a polynomial, which Ω absorbs
--   - reading: Ω(·), "for a constant prime p", "d = O(log n/log log n)" → ∀Δ ≥ 1, ∀C > 0, ∃c > 0, ∃n₀, ∀F, ∀p, ∀n ≥ n₀, ∀d ≤ C·log n/log log n; reason: c before F and p, since the explicit p² only has content with c uniform in p; after Δ because p.3 lists only n, d as growing; after C, the constant in the O
--   - reading: "n … the number of variables" (p.3) → n is the matrix width, with d·n² variables; reason: for d ≤ n the hypothesis and bound change by constants only; §7 uses n as the width
--   - reading: "in VP" → ∃K, ∀F, ∀n, d ≥ 1, a circuit of size ≤ K·(n·d)^K; reason: polynomial size in n and d, uniformly in the field
--   - encoding: "Let d = O(log n/log log n)", with d growing (p.3) → 2 ≤ d; reason: IMM_{n,1} is one variable with a one-edge circuit, so the bound fails at d = 1
--   - encoding: Δ ∈ ℕ → 1 ≤ Δ; reason: R(0) = 0, and 1/R(0) is undefined
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Theorem 1.2, p.4

import Mathlib
import Definitions.Def_SetMultCost_Circuit
import Definitions.Def_SetMultCost_Circuit_HasProductDepthLE
import Definitions.Def_SetMultCost_IsSetMultilinearOn
import Definitions.Def_SetMultCost_imm
import Definitions.Def_SetMultCost_fibF

universe u

namespace SetMultCost

/-- **Theorem 1.2 (Main Theorem).** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), p.4: "Fix a field F with char(F) = p, for a constant prime p.
Let ∆ ∈ N denote the product-depth parameter and let R(∆) = (F(∆ + 1) − 1). Let d = O(log n/ log log n).
There exists a set-multilinear polynomial P(x) in VP of degree-d such that the following holds over
F: Any product-depth ∆ circuit computing P(x) requires size at least exp (Ω(d^{1/R(∆)}/p²) · log n)."

**Formalization Note.** `P` is named: `IMM_{n,d}`, the polynomial the paper's proof bounds and its abstract
calls explicit. The first clause is "set-multilinear of degree `d`", the second is "in VP" (a polynomial
size circuit, uniformly in the field), the third is the bound.

In the third clause: `n` is the matrix width, while p.3 calls `n` the number of variables, `d n²` (the
hypotheses and bound change only by constants). `Φ` is any DAG of product-depth at most `Δ`, with equality
of polynomials, and is not assumed homogeneous or set-multilinear. `Ω` is `c`: chosen after the constants
`Δ` and `C`, the latter in `d ≤ C log n / log log n`, and before `F`, `p`, `n`, `d`, since the explicit
`p²` only has content if `c` does not depend on `p`. `d ≥ 2` because `d` is a growing parameter (p.3) and
`IMM_{n,1}` is one variable. `Δ ≥ 1` because `R(0) = 0`. -/
theorem theorem_1_2 :
    (∀ (F : Type u) [Field F] (n d : ℕ), 1 ≤ n → 1 ≤ d →
      IsSetMultilinearOn Prod.fst Finset.univ (imm F n d) ∧
      (imm F n d).IsHomogeneous d ∧ imm F n d ≠ 0) ∧
    (∃ K : ℕ, ∀ (F : Type u) [Field F] (n d : ℕ), 1 ≤ n → 1 ≤ d →
      ∃ Φ : Circuit (IMMVar n d) F, Φ.value = imm F n d ∧ Φ.size ≤ K * (n * d) ^ K) ∧
    (∀ Δ : ℕ, 1 ≤ Δ → ∀ C : ℝ, 0 < C → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ (F : Type u) [Field F] (p : ℕ), p.Prime → ∀ [CharP F p] (n d : ℕ), n₀ ≤ n → 2 ≤ d →
        (d : ℝ) ≤ C * Real.log n / Real.log (Real.log n) →
        ∀ Φ : Circuit (IMMVar n d) F, Φ.value = imm F n d → Φ.HasProductDepthLE Δ →
          Real.exp (c * (d : ℝ) ^ (1 / (R Δ : ℝ)) / (p : ℝ) ^ 2 * Real.log n) ≤ (Φ.size : ℝ)) := by sorry

end SetMultCost
