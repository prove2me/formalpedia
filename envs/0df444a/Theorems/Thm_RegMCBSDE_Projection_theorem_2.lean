-- Prove2me | Theorems.Thm_RegMCBSDE_Projection_theorem_2
-- name    : RegMCBSDE.Projection.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:39:12.909737+00:00
-- url     : https://prove2.me/theorems/2a8de6f4-4677-4562-83cf-982537372f27
-- title:
--   Theorem 2 — projection errors of the Picard–regression scheme accumulate additively
-- statement:
--   Assume (H1)–(H2). There are constants $C>0$ and $h_0>0$, depending only on $T,d,q,b,\sigma,f,C_f$ and the Lipschitz constant $L$ of (H1), with the following property. Let $N\ge1$ with $h=T/N<h_0$, let $S_0\in\mathbb R^d$, let the standing model hold on some probability space with a chain $P^N$ in $\mathbb R^{d'}$ and terminal function $\Phi^N$, and let the function bases $p_{l,k}$ have invertible Gram matrices. Let $I\ge1$, let $(Y^N,Z^N)$ be a solution of the discrete BSDE (5)–(6), and let $\alpha$ be a projection–Picard scheme with $I$ iterations, with iterates $Y^{N,I,I}$, $Z^{N,I,I}$. Then
--   $$\begin{aligned}\max_{0\le k\le N}\mathbb E|Y^{N,I,I}_{t_k}-Y^N_{t_k}|^2+h\sum_{k=0}^{N-1}\mathbb E|Z^{N,I,I}_{t_k}-Z^N_{t_k}|^2&\le Ch^{2I-2}\big[1+|S_0|^2+\mathbb E|\Phi^N(P^N_{t_N})|^2\big]\\&\quad+C\sum_{k=0}^{N-1}\mathbb E|\mathcal R_{p_{0,k}}(Y^N_{t_k})|^2+Ch\sum_{k=0}^{N-1}\sum_{l=1}^q\mathbb E|\mathcal R_{p_{l,k}}(Z^N_{l,t_k})|^2.\end{aligned}$$
--
--   The theorem says that the errors of the projection step only add up along the backward recursion, with a factor $C$ that does not grow as $N\to\infty$, and that they are measured by the projection residuals of the discrete BSDE itself, not of the scheme's own iterates. The Picard truncation contributes $h^{2I-2}$, so $I=2$ already matches the order of the time-discretization error.
--
--   **Formalization Note** The paper assumes (H1)–(H3); (H3) concerns the continuous terminal functional and is dropped. The constants $C$ and $h_0$ are chosen before every scheme parameter, including $N$, $I$, $S_0$, $d'$, the probability space and the bases. The maximum over $k$ is stated as a bound for every $k\le N$. $Z\in\mathbb R^q$ carries the Euclidean norm, and expectations are taken in $[0,\infty]$.
-- source:
--   Gobet, Lemor and Warin, A regression-based Monte Carlo method to solve backward stochastic differential equations, arXiv:math/0508491v1, p. 11, Theorem 2

import Mathlib
import Definitions.Def_RegMCBSDE_Projection_Scheme

namespace RegMCBSDE.Projection

open MeasureTheory ProbabilityTheory

/-- **Theorem 2** (Gobet–Lemor–Warin, arXiv:math/0508491v1, p. 11). Assume (H1)–(H2). For `h`
small enough,
`max_{0≤k≤N} 𝔼|Y^{N,I,I}_{t_k} - Y^N_{t_k}|^2 + h ∑_{k=0}^{N-1} 𝔼|Z^{N,I,I}_{t_k} - Z^N_{t_k}|^2
 ≤ C h^{2I-2} [1 + |S_0|^2 + 𝔼|Φ^N(P^N_{t_N})|^2] + C ∑_{k=0}^{N-1} 𝔼|ℛ_{p_{0,k}}(Y^N_{t_k})|^2
   + C h ∑_{k=0}^{N-1} ∑_{l=1}^q 𝔼|ℛ_{p_{l,k}}(Z^N_{l,t_k})|^2`.

Conventions: the generic `C` and the threshold `h₀` ("`h` small enough") depend only on
`(T, d, q, b, σ, f, C_f, L)` and are chosen before `N`, `I`, `S_0`, `d'`, the probability space,
`P^N`, `Φ^N` and the bases; `max_k` is "for every `k ≤ N`"; `I ≥ 1`; `(Y^N, Z^N)` is any solution
of (5)–(6) and `α` any family satisfying (9); `Z ∈ ℝ^q` with the Euclidean norm; expectations are
in `[0, ∞]`. (H3) concerns the continuous terminal functional, which does not enter the statement,
and is dropped. -/
theorem theorem_2 (T : ℝ) (hT : 0 < T) (d q : ℕ)
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
      ∀ (Y : ℕ → Ω → ℝ) (Z : ℕ → Ω → EuclideanSpace ℝ (Fin q)),
        IsDiscreteBSDE P 𝓕 T N b σ f S0 ΔW PN ΦN Y Z →
      ∀ α : ℕ → (k : ℕ) → (l : Fin (q + 1)) → Fin (n l k) → ℝ,
        IsProjectionScheme P T N b σ f S0 ΔW PN ΦN p I α →
      ∀ k ≤ N,
        ∫⁻ ω, ‖schemeY N PN ΦN p α I k ω - Y k ω‖ₑ ^ 2 ∂P
            + ENNReal.ofReal (T / N) * ∑ j ∈ Finset.range N,
                ∫⁻ ω, ‖schemeZ PN p α I j ω - Z j ω‖ₑ ^ 2 ∂P
          ≤ ENNReal.ofReal C * ENNReal.ofReal (T / N) ^ (2 * I - 2) * calA P N S0 PN ΦN
            + ENNReal.ofReal C * ∑ j ∈ Finset.range N,
                ∫⁻ ω, ‖resid P (basisAt p PN 0 j) (Y j) ω‖ₑ ^ 2 ∂P
            + ENNReal.ofReal C * ENNReal.ofReal (T / N) * ∑ j ∈ Finset.range N, ∑ m : Fin q,
                ∫⁻ ω, ‖resid P (basisAt p PN m.succ j) (fun ω' => Z j ω' m) ω‖ₑ ^ 2 ∂P := by sorry

end RegMCBSDE.Projection
