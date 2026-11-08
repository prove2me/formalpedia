-- Prove2me | Theorems.Thm_UniversalSubmod_theorem_2_4
-- name    : UniversalSubmod.theorem_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:52:36.314238+00:00
-- url     : https://prove2.me/theorems/d59928e2-9066-4345-996e-7dbbb1baf57a
-- title:
--   Theorem 2.4 — Gaussian rounding of near-orthogonal vectors with a random threshold gives $(1/4-\varepsilon)\max f$
-- statement:
--   Let $n,k\ge1$ be integers, $V=[n]$ and $0<\varepsilon<1/2$. Fix vectors $v_1,\dots,v_n\in\mathbb R^k$ with $\|v_i\|=1$ and
--   $$
--   \langle v_i,v_j\rangle\le\varepsilon\qquad(i\ne j).
--   $$
--   Let $Z=(Z_1,\dots,Z_k)$ be a $k$-variate standard Gaussian (independent coordinates) and let $T$ be a real random variable independent of $Z$ with mean $0$ and variance at most $\varepsilon$. Let $R_Z(T)=\{i\in V:\langle v_i,Z\rangle\ge T\}$. Then for every nonnegative submodular $f:2^V\to\mathbb R$,
--   $$
--   \mathbb E\big[f(R_Z(T))\big]\ \ge\ \Big(\frac14-\varepsilon\Big)\max_{S\subseteq V}f(S).
--   $$
--   Only an upper bound on the inner products is needed, and the law of $T$ is otherwise arbitrary.
--
--   This is the randomized version of the universal family: Theorem 1.1 derandomizes it on a grid.
--
--   **Formalization Note** $Z$ and $T$ are measurable maps on one probability space; $Z$ has law `stdGaussian` on `EuclideanSpace ℝ (Fin k)`, which is $N(0,I_k)$; $T$ is square integrable, $\mathbb E[T]=0$ and Mathlib's `variance T P` $\le\varepsilon$.
--
--   Differences from the source:
--   - encoding: $T$ of mean $0$ and variance at most $\varepsilon$ → $T$ measurable, `MemLp T 2 P`, $\int T=0$, `variance T P ≤ ε`; reason: a variance at most $\varepsilon$ presupposes $T\in L^2$; it keeps Mathlib's variance and integral from being junk values
--   - encoding: $Z$ a $k$-variate standard Gaussian with independent coordinates → $P\circ Z^{-1}=$ `stdGaussian (EuclideanSpace ℝ (Fin k))`; reason: the same law $N(0,I_k)$
--   - encoding: random variables and expectations → measurable maps on one probability space $(\Omega,P)$, expectations as Bochner integrals against $P$; reason: standing convention; every integrand is bounded or square integrable, so no integral is a junk value
--   - encoding: $\mathbb R^k$ with $\langle\cdot,\cdot\rangle$ and $\|\cdot\|$ → `EuclideanSpace ℝ (Fin k)` with its inner product and norm; reason: the same space
--   - encoding: the ground set $[n]$, subsets $S\subseteq[n]$, $f:2^{[n]}\to\mathbb R_{\ge0}$ → `Fin n`, `Finset (Fin n)`, a real-valued `f` with $f(S)\ge0$ for all $S$; reason: a relabelling of $[n]$; the same functions
--   - encoding: $\max_{S\subseteq[n]} f(S)$ → the published `OPT f` (a maximum over the nonempty finite family of all subsets); reason: the same number
-- source:
--   Adamczyk, Ueltzen, Vondrák, Optimal universal sets for submodular functions, manuscript (Nov. 3, 2026; sha256 8a53c0912e8ad39b1019cbabfbde98980fd3eea456a8c7e5b28eb55d58343714), Theorem 2.4, p.7 (proof p.10)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_UniversalSubmod_threshSet

namespace UniversalSubmod

open MeasureTheory ProbabilityTheory NonmonotoneSubmod.Shared
open scoped RealInnerProductSpace

/-- **Theorem 2.4** (Gaussian rounding of near-orthogonal vectors; Adamczyk, Ueltzen, Vondrák,
*Optimal universal sets for submodular functions*, manuscript of November 3, 2026, Theorem 2.4,
p.7; proof p.10). Let `n, k ≥ 1`, `V = [n]` and `0 < ε < 1/2`. Fix `v₁, …, vₙ ∈ ℝ^k` with
`‖vᵢ‖ = 1` and `⟨vᵢ, vⱼ⟩ ≤ ε` for `i ≠ j`. Let `Z` be a `k`-variate standard Gaussian and `T` an
independent random variable of mean `0` and variance at most `ε`, and
`R_Z(T) = {i ∈ V : ⟨vᵢ, Z⟩ ≥ T}`. Then for every nonnegative submodular `f : 2^V → ℝ`,
`E[f(R_Z(T))] ≥ (1/4 − ε) max_{S⊆V} f(S)`.

**Formalization Note.** `Z` and `T` live on one probability space; `Z` has law
`stdGaussian (EuclideanSpace ℝ (Fin k))` (= `N(0, I_k)`, independent standard coordinates); `T` is
measurable and square integrable (implied by "variance at most `ε`"; it makes Mathlib's `variance`
and `∫` genuine), with `E[T] = 0` and `Var T ≤ ε`. The law of `T` is otherwise arbitrary. The
inner-product bound is one-sided, as printed. -/
theorem theorem_2_4 (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (hv : ∀ i, ‖v i‖ = 1)
    (hvv : ∀ i j, i ≠ j → ⟪v i, v j⟫ ≤ ε)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → EuclideanSpace ℝ (Fin k)) (hZ : Measurable Z)
    (hZlaw : P.map Z = stdGaussian (EuclideanSpace ℝ (Fin k)))
    (T : Ω → ℝ) (hT : Measurable T) (hind : IndepFun Z T P) (hT2 : MemLp T 2 P)
    (hT0 : ∫ ω, T ω ∂P = 0) (hTvar : variance T P ≤ ε)
    (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) :
    (1 / 4 - ε) * OPT f ≤ ∫ ω, f (threshSet v (Z ω) (T ω)) ∂P := by sorry

end UniversalSubmod
