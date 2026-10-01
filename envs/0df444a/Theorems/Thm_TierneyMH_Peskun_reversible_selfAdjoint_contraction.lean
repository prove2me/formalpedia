-- Prove2me | Theorems.Thm_TierneyMH_Peskun_reversible_selfAdjoint_contraction
-- name    : TierneyMH.Peskun.reversible_selfAdjoint_contraction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T12:32:21.73715+00:00
-- url     : https://prove2.me/theorems/c0cb1eb9-a057-4954-9c05-748a075abb82
-- title:
--   A reversible kernel is a self-adjoint contraction on $L^2_0(\pi)$
-- statement:
--   Let $\pi$ be a probability measure on a measurable space $E$ and let $H$ be a Markov transition kernel on $E$ that is reversible with respect to $\pi$, i.e. $\pi(dx)H(x,dy) = \pi(dy)H(y,dx)$. Let $L^2_0(\pi) = \{g \in L^2(\pi) : \int g\,d\pi = 0\}$ and write $(Hf)(x) = \int f(y)\,H(x,dy)$ and $\langle f, g\rangle = \int fg\,d\pi$. Then $H$ represents a self-adjoint operator on $L^2_0(\pi)$ with spectral radius at most one. Explicitly, for all $f, g \in L^2_0(\pi)$:
--
--   1. $Hf \in L^2(\pi)$ and $\int Hf\, d\pi = 0$, so $H$ maps $L^2_0(\pi)$ into itself;
--   2. $\langle Hf, g\rangle = \langle f, Hg\rangle$;
--   3. $\langle Hf, Hf \rangle \le \langle f, f\rangle$.
--
--   $$
--   \langle Hf, g\rangle = \langle f, Hg\rangle, \qquad \|Hf\|_{L^2(\pi)} \le \|f\|_{L^2(\pi)} .
--   $$
--
--   These are the facts that allow the spectral theorem to be applied to $H$ in the proof of Theorem 4.
--
--   **Formalization Note** For a bounded self-adjoint operator the spectral radius equals the operator norm, so the norm bound (3) is the paper's "spectral radius bounded by one". Reversibility is Mathlib's `Kernel.IsReversible`, detailed balance on measurable rectangles, which implies invariance of $\pi$. $f$ and $g$ are measurable representatives of their $L^2$ classes.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 5, proof of Theorem 4 (first sentence after citing Kipnis and Varadhan)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace TierneyMH.Peskun

/-- **Proof of Theorem 4** (Tierney 1998, p. 5): a reversible transition kernel `H` with
invariant distribution `π` represents a self-adjoint operator on
`L²₀(π) = {g ∈ L²(π) : ∫ g dπ = 0}` with spectral radius bounded by one.
Writing `(Hf)(x) = ∫ f(y) H(x, dy)`, for all `f, g ∈ L²₀(π)`:
1. `Hf ∈ L²(π)` and `∫ Hf dπ = 0` (so `H` maps `L²₀(π)` into itself);
2. `⟨Hf, g⟩ = ⟨f, Hg⟩` (self-adjointness);
3. `⟨Hf, Hf⟩ ≤ ⟨f, f⟩` (norm at most one).
For a self-adjoint bounded operator the spectral radius equals the operator norm, so (3) is
the paper's spectral-radius bound. Reversibility is `Kernel.IsReversible H π`, which is
detailed balance (2) on measurable rectangles and implies invariance. -/
theorem reversible_selfAdjoint_contraction {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hH : Kernel.IsReversible H π)
    (f g : E → ℝ) (hf_meas : Measurable f) (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π = 0)
    (hg_meas : Measurable g) (hg : MemLp g 2 π) (hg0 : ∫ x, g x ∂π = 0) :
    MemLp (fun x => ∫ y, f y ∂(H x)) 2 π ∧
      ∫ x, (∫ y, f y ∂(H x)) ∂π = 0 ∧
      ∫ x, (∫ y, f y ∂(H x)) * g x ∂π = ∫ x, f x * (∫ y, g y ∂(H x)) ∂π ∧
      ∫ x, (∫ y, f y ∂(H x)) ^ 2 ∂π ≤ ∫ x, f x ^ 2 ∂π := by sorry

end TierneyMH.Peskun
