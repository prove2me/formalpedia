-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_lemma_3_1
-- name    : StochKolmogorov.Persist.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:17.708989+00:00
-- url     : https://prove2.me/theorems/aaf23e78-2b6a-4eec-82a3-238baed9491d
-- title:
--   Lemma 3.1, p. 14 — (1.1) has a pathwise unique strong solution, the faces ℝ^{I,◦}₊ are invariant, H < ∞, and 𝔼ₓV^{δ₀}(X(t)) ≤ exp(δ₀Ht)V^{δ₀}(x)
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i=X_if_i(X)\,dt+X_ig_i(X)\,dE_i$, $E=\Gamma^\top B$, $\Sigma=\Gamma^\top\Gamma=(\sigma_{ij})$, on $\mathbb R^n_+=[0,\infty)^n$ ($n\ge1$ populations), $\mathbb P_x,\mathbb E_x$ refer to the solution started at $x$, $\|x\|=\sum_i|x_i|$, and Assumption 1.1 is in force.
--
--   Let $B$ be an $n$-dimensional standard Brownian motion on a probability space. Then:
--
--   1. for every $x\in\mathbb R^n_+$, (1.1) driven by $B$ has a strong solution with $X(0)=x$;
--   2. any two such solutions are indistinguishable (pathwise uniqueness);
--   3. for every $I\subseteq\{1,\dots,n\}$ and $x\in\mathbb R^{I,\circ}_+=\{x\in\mathbb R^n_+:x_i=0\ (i\notin I),\ x_i>0\ (i\in I)\}$, the solution from $x$ stays in $\mathbb R^{I,\circ}_+$ for all $t\ge0$ with probability one;
--   4. for every $\delta_0$ as in (3.2), the constant $H$ of (3.5) is finite, and for every $p\in\mathbb R^{n,\circ}_+$ with $\|p\|\le\delta_0$, every $x\in\mathbb R^{n,\circ}_+$ and every $t\ge0$, with $V(x)=(1+c^\top x)/\prod_ix_i^{p_i}$,
--   $$\mathbb E_xV^{\delta_0}(X(t))\le e^{\delta_0Ht}\,V^{\delta_0}(x).\tag{3.6}$$
--
--   Well-posedness and invariance of the faces make the boundary $\partial\mathbb R^n_+$ and each face absorbing, which is why ergodic measures on the boundary exist; (3.6) is the a priori moment bound behind the Lyapunov estimates of §4.
--
--   **Formalization Note** Existence is stated on the given Brownian motion and probability space (a strong solution). Uniqueness and invariance are stated for every solution from $x$. Finiteness of $H$ ("$<\infty$" in (3.5)) is stated as boundedness above of the bracket on $\mathbb R^n_+$, so that $H$ is the true supremum. The expectation in (3.6) is a lower Lebesgue integral of the nonnegative quantity $V^{\delta_0}$, so no integrability hypothesis is needed. Coordinates are indexed by `Fin n`; $n\ge1$.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 3.1, p. 14, with (3.2), (3.4), (3.5), pp. 13–14

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

open EthierKurtz

/-- Lemma 3.1 (p. 14), with (3.5): well-posedness of (1.1) on the given Brownian motion,
invariance of the faces `ℝ^{I,◦}₊`, finiteness of `H` and the moment bound (3.6). -/
theorem lemma_3_1 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (hB : IsStandardBrownian P B) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    -- existence of a strong solution from every `x ∈ ℝⁿ₊`
    (∀ x ∈ orthant n, ∃ Y : ℝ≥0 → Ω → SDEState n,
      SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y) ∧
    -- pathwise uniqueness
    (∀ x ∈ orthant n, ∀ Y Y' : ℝ≥0 → Ω → SDEState n,
      SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y →
      SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y' →
      ∀ᵐ ω ∂P, ∀ t, Y t ω = Y' t ω) ∧
    -- the solution started in `ℝ^{I,◦}₊` stays there forever with probability one
    (∀ I : Finset (Fin n), ∀ x ∈ faceOpen I, ∀ Y : ℝ≥0 → Ω → SDEState n,
      SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y →
      ∀ᵐ ω ∂P, ∀ t, Y t ω ∈ faceOpen I) ∧
    -- `H < ∞` in (3.5), and (3.6)
    (∀ δ₀ : ℝ, IsDelta0 C γb δ₀ →
      BddAbove ((bracket35 C c γb δ₀) '' orthant n) ∧
      ∀ p ∈ openOrthant n, l1 p ≤ δ₀ → ∀ x ∈ openOrthant n, ∀ Y : ℝ≥0 → Ω → SDEState n,
        SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y → ∀ t : ℝ≥0,
          ∫⁻ ω, ENNReal.ofReal (Vfun c p (Y t ω) ^ δ₀) ∂P ≤
            ENNReal.ofReal (Real.exp (δ₀ * Hconst C c γb δ₀ * t) * Vfun c p x ^ δ₀)) := by sorry

end StochKolmogorov.Persist
