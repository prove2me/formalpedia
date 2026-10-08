-- Prove2me | Theorems.Thm_WassDDRO_Extremal_objective13_le_expect
-- name    : WassDDRO.Extremal.objective13_le_expect
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:56:50.989011+00:00
-- url     : https://prove2.me/theorems/4b755cf5-cda0-4613-9a8a-e5a64431da5e
-- title:
--   Proof of Theorem 4.4, p. 17 — for Q = (1/N)ΣΣ α_ik δ_{ξ_ik}, E^Q[ℓ(ξ)] = (1/N)ΣΣ α_ik ℓ(ξ_ik) ≥ the objective of (13) at a feasible point
-- statement:
--   Let $N \ge 1$, let $\ell_1,\dots,\ell_K : E \to \overline{\mathbb R}$ be measurable and never $+\infty$, and let $\ell = \max_k \ell_k$. For every feasible point $(\alpha_{ik}, q_{ik})$ of program (13), with $\xi_{ik} = \hat\xi_i - q_{ik}/\alpha_{ik}$ and $\mathbb Q = \frac1N\sum_{i,k}\alpha_{ik}\delta_{\xi_{ik}}$,
--   $$\mathbb E^{\mathbb Q}[\ell(\xi)] \ =\ \frac1N\sum_{i=1}^N\sum_{k=1}^K \alpha_{ik}\,\ell(\xi_{ik}) \qquad\text{and}\qquad \frac1N\sum_{i=1}^N\sum_{k=1}^K \alpha_{ik}\,\ell_k(\xi_{ik}) \ \le\ \mathbb E^{\mathbb Q}[\ell(\xi)].$$
--
--   The equality is the expectation of $\ell$ under a discrete distribution (the middle equality of the paper's chain on p. 17), and the inequality follows the paper's estimate $\ell \ge \ell_k$. Together with the previous milestone it gives the lower bound $\sup_{\mathbb Q \in \mathbb B_\varepsilon(\widehat{\mathbb P}_N)} \mathbb E^{\mathbb Q}[\ell(\xi)] \ge \limsup_r \mathbb E^{\mathbb Q_r}[\ell(\xi)]$ chain in the proof of Theorem 4.4.
--
--   **Formalization Note** The expectation is the extended expectation of p. 5 (the positive and negative parts are integrated separately, with $\infty - \infty = \infty$). The $ik$-th term on either side is $0$ when $\alpha_{ik} = 0$ (the convention of p. 14).
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, proof of Theorem 4.4 (second claim), p. 17

import Mathlib
import Definitions.Def_WassDDRO_Extremal_Setting

namespace WassDDRO.Extremal

/-- Proof of Theorem 4.4, p. 17: for any feasible point (α, q) of (13), the expectation of
ℓ = max_k ℓ_k under Q = (1/N) Σᵢ Σ_k α_ik δ_{ξ_ik} equals (1/N) Σᵢ Σ_k α_ik ℓ(ξ_ik) (the term
being 0 when α_ik = 0), and by ℓ ≥ ℓ_k this dominates the objective (1/N) Σᵢ Σ_k α_ik ℓ_k(ξ_ik)
of (13). -/
theorem objective13_le_expect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (hne_top : ∀ k ξ, ℓ k ξ ≠ ⊤)
    (ξhat : Fin N → E) (ε : ℝ)
    (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E) (h : Feasible13 ε Ξ ξhat α q) :
    DupacovaWets.Consistency.expect (discreteQ ξhat α q) (maxLoss ℓ) =
        ((1 / (N : ℝ) : ℝ) : EReal) * ∑ i, ∑ k, term13 (maxLoss ℓ) (ξhat i) (α i k) (q i k) ∧
      objective13 ξhat ℓ α q ≤
        DupacovaWets.Consistency.expect (discreteQ ξhat α q) (maxLoss ℓ) := by sorry

end WassDDRO.Extremal
