-- Prove2me | Theorems.Thm_Reiman84_QueueLength_proposition_3
-- name    : Reiman84.QueueLength.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:06:17.813323+00:00
-- url     : https://prove2.me/theorems/1fb81528-3d9d-419e-b1a9-333c56a1ffb3
-- title:
--   Proposition 3 — ζⁿ ⇒ ζ, Brownian motion with drift c and covariance 𝒜
-- statement:
--   Consider a sequence of networks of §2 satisfying the heavy-traffic conditions (20)–(26), with common routing matrix $P$, and let $X^n(t)=A^n(t)+\sum_k\hat S^n_k(t)$ and $\zeta^n(t)=n^{-1/2}X^n(nt)$, $0\le t\le1$. Let $\zeta$ be a $K$-dimensional Brownian motion with drift $c$ and covariance matrix $\mathcal A$ given by (27)–(28). Then
--   $$\zeta^n\Rightarrow\zeta\quad\text{in } D \text{ as } n\to\infty.\qquad(29)$$
--
--   This is the functional central limit theorem for the netput process, combining the arrival, service and routing fluctuations of Lemmas 3–5.
--
--   **Formalization Note** The statement is made for every Brownian motion $\zeta$ with these parameters (they all have the same law). Weak convergence in $D$ is in coupling form (see the definition file).
-- source:
--   Reiman, Open Queueing Networks in Heavy Traffic, Math. Oper. Res. 9(3) (1984), p. 449, Proposition 3 (Eq. (29), p. 447)

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_Reiman84_QueueLength_Network
import Definitions.Def_Reiman84_QueueLength_HeavyTraffic

namespace Reiman84.QueueLength

open Filter Topology MeasureTheory

/-- Proposition 3, p. 449 (Eq. (29)): under (20)–(26), `ζⁿ ⇒ ζ` in `D`, where
`ζⁿ(t) = n^{-1/2} Xⁿ(nt)` and `ζ` is a `K`-dimensional Brownian motion with drift `c` and
covariance `𝒜`. -/
theorem proposition_3 {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)} (net : ∀ n, Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ)
    (hA : HeavyTrafficAssumptions net R mu s lam a c)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (ζ : Ω' → ℝ → Fin K → ℝ)
    (hζ : IsDriftedBM c (covA lam a mu s R) P' ζ) :
    WeakConvD P (fun n ω => diffScale n (fun t => (net n).X t ω)) P' ζ := by sorry

end Reiman84.QueueLength
