-- Prove2me | Theorems.Thm_RegMCBSDE_Projection_eq_19_uniform_L2_bounds
-- name    : RegMCBSDE.Projection.eq_19_uniform_L2_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:37.500994+00:00
-- url     : https://prove2.me/theorems/8b0be70f-91b1-4ccf-93a6-a9a79bbad139
-- title:
--   Proof of Theorem 2, Step 2, Eq. (19) — uniform L2 bounds E|Y^{N,i,I}_{t_k}|² + h E|Z^{N,i,I}_{l,t_k}|² ≤ C A^N(S_0)
-- statement:
--   Assume (H1)–(H2). There are constants $C>0$ and $h_0>0$, depending only on $T,d,q,b,\sigma,f,C_f$ and the Lipschitz constant $L$ of (H1), with the following property. Let $N\ge1$ with $h=T/N<h_0$, let $S_0\in\mathbb R^d$, let the standing model hold on some probability space with a chain $P^N$ in $\mathbb R^{d'}$ and terminal function $\Phi^N$, and let the bases have invertible Gram matrices. Then for every $I\ge1$ and every projection–Picard scheme $\alpha$ with $I$ iterations,
--   $$\sup_{I\ge1}\ \sup_{i\ge0}\ \sup_{0\le k\le N-1}\Big(\mathbb E|Y^{N,i,I}_{t_k}|^2+h\,\mathbb E|Z^{N,i,I}_{l,t_k}|^2\Big)\le C\,\mathcal A^N(S_0)\qquad(1\le l\le q),$$
--   where $\mathcal A^N(S_0)=1+|S_0|^2+\mathbb E|\Phi^N(P^N_{t_N})|^2$.
--
--   The bound shows that neither the Picard iterations nor the backward recursion amplify the size of the data, uniformly in the number of time steps, the number of iterations and the choice of bases.
--
--   **Formalization Note** The generic constant $C$ and the threshold $h_0$ of "$h$ small enough" are chosen before $N$, $I$, $i$, $k$, $S_0$, $d'$, the probability space, $P^N$, $\Phi^N$ and the bases. The free index $l$ of the paper's display is read as "for every $1\le l\le q$". The paper's $\sup_{0\le k\le N}$ is restricted to $k\le N-1$, where $Z$ is defined; at $k=N$ the $Y$-term is $\mathbb E|\Phi^N(P^N_{t_N})|^2\le\mathcal A^N(S_0)$. Expectations are taken in $[0,\infty]$.
-- source:
--   Gobet, Lemor and Warin, A regression-based Monte Carlo method to solve backward stochastic differential equations, arXiv:math/0508491v1, p. 13, Proof of Theorem 2, Step 2, Eq. (19); p. 11 (A^N(S_0))

import Mathlib
import Definitions.Def_RegMCBSDE_Projection_Scheme

namespace RegMCBSDE.Projection

open MeasureTheory ProbabilityTheory

/-- **Proof of Theorem 2, Step 2, Eq. (19)** (arXiv:math/0508491v1, p. 13): uniform `𝐋₂` bounds
on the projection-Picard iterates,
`sup_{I ≥ 1} sup_{i ≥ 0} sup_k (𝔼|Y^{N,i,I}_{t_k}|^2 + h 𝔼|Z^{N,i,I}_{l,t_k}|^2) ≤ C 𝒜^N(S_0)`,
with `𝒜^N(S_0) = 1 + |S_0|^2 + 𝔼|Φ^N(P^N_{t_N})|^2` and `h = T/N`.

The generic constant `C` and the threshold `h₀` of "`h` small enough" are chosen after the data
`(T, d, q, b, σ, f, C_f, L)` and before `N`, `I`, `i`, `k`, `S_0`, `d'`, the probability space,
the chain `P^N`, `Φ^N` and the bases. The free index `l` is read as "for every `1 ≤ l ≤ q`"
(component `m : Fin q` is `l = m + 1`); `k` ranges over `0 ≤ k ≤ N - 1`, where `Z` is defined. -/
theorem eq_19_uniform_L2_bounds (T : ℝ) (hT : 0 < T) (d q : ℕ)
    (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (σ : ℝ → EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin q) ℝ)
    (f : ℝ → EuclideanSpace ℝ (Fin d) → ℝ → EuclideanSpace ℝ (Fin q) → ℝ)
    (Cf L : ℝ) (hH1 : H1 T L b σ) (hH2 : H2 T Cf f) :
    ∃ C : ℝ, 0 < C ∧ ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ (d' : ℕ) (S0 : EuclideanSpace ℝ (Fin d)) (N : ℕ), 0 < N → T / N < h₀ →
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (𝓕 : Filtration ℕ mΩ) (ΔW : ℕ → Ω → EuclideanSpace ℝ (Fin q))
        (PN : ℕ → Ω → EuclideanSpace ℝ (Fin d')) (ΦN : EuclideanSpace ℝ (Fin d') → ℝ),
      IsStandingModel P 𝓕 T N b σ S0 ΔW PN ΦN →
      ∀ (n : Fin (q + 1) → ℕ → ℕ)
        (p : (l : Fin (q + 1)) → (k : ℕ) → EuclideanSpace ℝ (Fin d') → Fin (n l k) → ℝ),
      IsBasis P N PN n p →
      ∀ I : ℕ, 1 ≤ I →
      ∀ α : ℕ → (k : ℕ) → (l : Fin (q + 1)) → Fin (n l k) → ℝ,
        IsProjectionScheme P T N b σ f S0 ΔW PN ΦN p I α →
      ∀ (i k : ℕ), k < N → ∀ m : Fin q,
        ∫⁻ ω, ‖schemeY N PN ΦN p α i k ω‖ₑ ^ 2 ∂P
            + ENNReal.ofReal (T / N) * ∫⁻ ω, ‖schemeZ PN p α i k ω m‖ₑ ^ 2 ∂P
          ≤ ENNReal.ofReal C * calA P N S0 PN ΦN := by sorry

end RegMCBSDE.Projection
