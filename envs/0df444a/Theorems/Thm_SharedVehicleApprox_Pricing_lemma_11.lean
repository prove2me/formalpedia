-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_lemma_11
-- name    : SharedVehicleApprox.Pricing.lemma_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:15.571003+00:00
-- url     : https://prove2.me/theorems/9a497421-cb29-420d-95a1-09126007732d
-- title:
--   Lemma 11, p. 16 — for a balanced state-independent policy, Obj_∞(q) = Ôbj(q) (corrected: support of q strongly connected)
-- statement:
--   Let $\varphi_{ij}\ge0$ be arrival rates on $n\ge1$ nodes, $I_{ij}$ per-ride rewards with reward curves $R_{ij}(q)=q\,I_{ij}(q)$, and $q\in[0,1]^{n\times n}$ a state-independent quantile matrix with balanced demand whose support graph $\{(a,b):a\ne b,\ \varphi_{ab}q_{ab}>0\}$ is strongly connected. For every positive solution $r$ of the traffic equations of $q$, the infinite-unit objective equals the elevated objective:
--   $$\mathrm{Obj}_\infty(q)=\sum_i\frac{r_i}{\max_jr_j}\sum_j\varphi_{ij}R_{ij}(q_{ij})=\sum_{i,j}\varphi_{ij}R_{ij}(q_{ij})=\widehat{\mathrm{Obj}}(q).$$
--
--   Applied to the relaxation optimum $\tilde q$, this identifies the value of Algorithm 1 with the infinite-unit objective of its prices.
--
--   Differences from the source:
--   - correction: no connectivity hypothesis → hypothesis SupportConnected φ q; reason: the printed statement is false without it: n = 2, φ ≡ 1, I ≡ 1, q = (1, 0, 0, 1) is balanced and r = (1, 2) solves its traffic equations, so Obj_∞(q) = 1/2 + 1 = 3/2 ≠ 2 = Ôbj(q); the paper's proof uses Lemma 10, which assumes irreducibility
--   - generalization: r = r(q), the traffic intensities of q → any positive solution r of the rate-form traffic equations; reason: r(q) is such a solution (proof of Proposition 8, p. 14), so the statement specializes to it
--   - encoding: Obj_∞(q), the objective in the infinite-unit system → Σ_i (r_i/r_max) B_i(q) with B_i(q) = Σ_j φ_ij R_ij(q_ij); reason: this is the formula of the proof of Lemma 12 (p. 16), with the infinite-unit availabilities of Proposition 6
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 16 (PDF 17), Lemma 11

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

open Finset QueueingFundamentals.Networks Filter Topology

namespace SharedVehicleApprox.Pricing

/-- Lemma 11, p. 16: for a state-independent `q` with strongly connected support satisfying
balanced demand, the infinite-unit objective equals the elevated objective:
`Obj_∞(q) = Ôbj(q)`. -/
theorem lemma_11 {n : ℕ} [NeZero n] (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (I : Fin n → Fin n → ℝ → ℝ) (q : Fin n → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ 1)
    (hbal : IsBalanced φ q) (hconn : SupportConnected φ q)
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (htr : IsTraffic φ q r) :
    objInf φ I q r = elevObj φ I q := by sorry

end SharedVehicleApprox.Pricing
