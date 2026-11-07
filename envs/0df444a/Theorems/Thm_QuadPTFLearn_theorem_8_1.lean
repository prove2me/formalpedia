-- Prove2me | Theorems.Thm_QuadPTFLearn_theorem_8_1
-- name    : QuadPTFLearn.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:26:08.131895+00:00
-- url     : https://prove2.me/theorems/c9671c98-5d94-4fd4-8e44-ffa64790ada4
-- title:
--   Theorem 8.1, p.72 (corrected: $L=k^2\log^3(2k)\log^2(1/\epsilon)$ and $(n+1)$ for $n$) — hinge-loss learning in a known lifted subspace
-- statement:
--   **Learning in a known lifted subspace.** Let $d,k\ge1$, $\epsilon\in(0,1/2)$ and
--   $$L=k^2\log^3(2k)\log^2(1/\epsilon).$$
--   Let $\Phi_2:\mathbb R^d\to\mathbb R^N$, $N=d(d+3)/2$, be the normalized Gaussian Hermite polynomials of degrees one and two, and $S\subseteq\mathbb R^N$ a subspace of dimension $n$. Suppose $D$ is a joint distribution of $(x,y)$ over $\mathbb R^d\times\{\pm1\}$ with $D_x=N(0,I_d)$, and there is an intersection $f(x)=\bigwedge_{i=1}^k\mathrm{sign}(c_i+u_i\cdot\Phi_2(x))$ with $c_i\in\mathbb R$, $u_i\in S$, such that $\Pr_{(x,y)\sim D}[f(x)\ne y]\le2^{-CL}$.
--
--   Then there is an algorithm which, given $d,k,\epsilon$, a basis of $S$ and i.i.d. samples from $D$, has sample complexity and running time at most
--   $$d^{O(1)}\,(n+1)^{O(k^2\log^2(2k)\log(1/\epsilon))}\,2^{O(k^2\log^3(2k)\log^2(1/\epsilon))}$$
--   and with probability at least $2/3$ outputs a hypothesis $h:\mathbb R^d\to\{\pm1\}$ with $\Pr_{(x,y)\sim D}[h(x)\ne y]\le\epsilon$.
--
--   The theorem is the final stage of the main learner: once a low-dimensional lifted subspace is known, hinge-loss minimization over polynomials of its features learns the target with quasipolynomial dependence on $1/\epsilon$.
--
--   **Formalization Note** The noise constant $C$ and the bound constants are universal and chosen with the program. The basis is input after $(k,\epsilon,n)$ in the lifted-vector layout. The output is decoded as a PTF of quadratic features $H$ and $h=2H-1$; $\mathrm{sign}(0)=1$.
--
--   Differences from the source:
--   - correction: L = k² log³(k) log²(1/ϵ) → L = k² log³(2k) log²(1/ϵ); reason: at k = 1 the printed L is 0 and the noise bound 2^{−CL} = 1 is vacuous: with k = d = 1, D having x ∼ N(0,1) and y a fair ±1 coin independent of x, and f = sign(1 + 0·Φ₂), every hypothesis has error 1/2 > ϵ; log(2k) is the L of the proof of Theorem 9.1 (p.91) and of the bound
--   - correction: n^{O(k² log²(2k) log(1/ϵ))} → (n + 1)^{O(k² log²(2k) log(1/ϵ))}; reason: for n = dim S = 0 the printed bound is 0, below the one step every run takes (e.g. S = {0}, f ≡ 1, y ≡ 1 satisfies every hypothesis); the proof's own count uses M ≤ (n + 1)^t (p.81)
--   - reading: "there is an algorithm … using … samples and time", model unspecified → one admissible program of the deterministic arithmetic sampling real RAM (exact + − × ÷, comparisons, pointers; no √, exp, log, floor, coin; unit cost, `sample` costs d+1), chosen before every parameter and the distribution, with samples and work bounded on every sample stream; reason: the paper fixes no model and its proofs count arithmetic operations; a single uniform program with worst-case bounds is the non-weaker reading
--   - generalization: outputs a hypothesis h : ℝᵈ → {±1} → output memory decoding to a PTF of quadratic features H, with h = 2H − 1; an undecodable output is a failure; reason: Algorithm 5 returns sign⟨ŵ, Ψ_t(x)⟩ with Ψ_t monomials in the quadratic features ⟨v_j, Φ₂(x)⟩, which has this form; every such h is a hypothesis
--   - encoding: 2^{−CL}; d^{O(1)} n^{O(…)} 2^{O(…)} → 2^{−C₀L} and d^C (n+1)^{C k² log²(2k) log(1/ϵ)} 2^{C k² log³(2k) log²(1/ϵ)} for both samples and work, universal C₀, C chosen with the program, natural log; reason: the meaning of the constants
--   - encoding: given d, k, ϵ, a basis for S → input [k, ϵ, n] followed by any linearly independent family of n vectors of ℝᴺ spanning S, in the lifted-vector layout; d is the machine's dimension; reason: input convention
--   - encoding: D over ℝᵈ × {±1} with D_x = N(0, I_d); d, k ∈ ℤ₊ → a probability law on ℝᵈ × ℝ with marginal N(0, I_d), labels in {±1} a.s.; 1 ≤ d, 1 ≤ k; reason: the same laws
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Theorem 8.1 (Learning in a known lifted subspace), p.72 (PDF p.74); proof and Algorithm 5, pp.79–81 (PDF pp.81–83)

import Mathlib
import Definitions.Def_QuadPTFLearn_Learner

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Theorem 8.1 (Learning in a known lifted subspace), p.72 (PDF p.74), corrected:
`L = k² log³(2k) log²(1/ϵ)` and `(n + 1)` in place of `n` in the bound.

Let `d, k ≥ 1`, `ϵ ∈ (0, 1/2)`, `L = k² log³(2k) log²(1/ϵ)`, `Φ₂ : ℝᵈ → ℝᴺ` the normalized
Hermite features of degrees one and two, and `S ⊆ ℝᴺ` a subspace of dimension `n`. Suppose `D`
is a law of `(x, y)` on `ℝᵈ × {±1}` with `D_x = N(0, I_d)` and there is
`f(x) = ⋀ᵢ sign(cᵢ + uᵢ · Φ₂(x))`, `uᵢ ∈ S`, with `Pr_D[f(x) ≠ y] ≤ 2^{−CL}`. Given `d, k, ϵ`, a
basis of `S` and samples, the algorithm uses at most
`d^{O(1)} (n+1)^{O(k² log²(2k) log(1/ϵ))} 2^{O(k² log³(2k) log²(1/ϵ))}` samples and time and,
with probability at least `2/3`, outputs `h : ℝᵈ → {±1}` with `Pr_D[h(x) ≠ y] ≤ ϵ`.

**Formalization Note.** One program; the noise constant `C₀` and the bound constant `C` are
chosen before `d, k, ϵ, S, D`. Input: `[k, ϵ, n]` followed by the basis vectors in the
`liftCells` layout (any basis of `S`). `sign(0) = 1` (§2). The output is decoded as a PTF of
quadratic features `H` and `h = 2 H − 1`. -/
theorem theorem_8_1 :
    ∃ P : Program, Admissible P ∧ ∃ C₀ C : ℕ,
      ∀ d k : ℕ, 1 ≤ d → 1 ≤ k → ∀ ϵ : ℝ, 0 < ϵ → ϵ < 1 / 2 →
      ∀ (n : ℕ) (e : Fin n → Lift d), LinearIndependent ℝ e →
      ∀ (D : Measure (Pt d × ℝ)) [IsProbabilityMeasure D], HasGaussMarginal D →
        (∀ᵐ z ∂D, z.2 = 1 ∨ z.2 = -1) →
        (∃ c : Fin k → ℝ, ∃ u : Fin k → Lift d,
          (∀ i, u i ∈ Submodule.span ℝ (Set.range e)) ∧
          D {z | (if ∀ i, 0 ≤ c i + ⟪u i, phi2 z.1⟫ then (1 : ℝ) else -1) ≠ z.2} ≤
            ENNReal.ofReal ((2 : ℝ) ^ (-((C₀ : ℝ) * ((k : ℝ) ^ 2 * Real.log (2 * k) ^ 3 *
              Real.log (1 / ϵ) ^ 2))))) →
        HaltsWithin P (d + 1)
            (initState (d + 1) ([(k : ℝ), ϵ, (n : ℝ)] ++
              (List.finRange n).flatMap (fun j => liftCells (e j))))
            ((d : ℝ) ^ C * ((n : ℝ) + 1) ^ ((C : ℝ) * (k : ℝ) ^ 2 * Real.log (2 * k) ^ 2 *
                Real.log (1 / ϵ)) *
              (2 : ℝ) ^ ((C : ℝ) * (k : ℝ) ^ 2 * Real.log (2 * k) ^ 3 * Real.log (1 / ϵ) ^ 2))
            ((d : ℝ) ^ C * ((n : ℝ) + 1) ^ ((C : ℝ) * (k : ℝ) ^ 2 * Real.log (2 * k) ^ 2 *
                Real.log (1 / ϵ)) *
              (2 : ℝ) ^ ((C : ℝ) * (k : ℝ) ^ 2 * Real.log (2 * k) ^ 3 * Real.log (1 / ϵ) ^ 2)) ∧
        SucceedsWP P (d + 1)
          (initState (d + 1) ([(k : ℝ), ϵ, (n : ℝ)] ++
            (List.finRange n).flatMap (fun j => liftCells (e j))))
          (Measure.infinitePi (fun _ : ℕ => jointLaw D)) (2 / 3)
          (fun s => ∃ H : Hyp d, decode d (outMem s) (outBase s) = some H ∧
            D {z | 2 * H.eval z.1 - 1 ≠ z.2} ≤ ENNReal.ofReal ϵ) := by sorry

end QuadPTFLearn
