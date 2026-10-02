-- Prove2me | Theorems.Thm_Transcendence_taylor_tail_le
-- name    : Transcendence.taylor_tail_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:19:17.143077+00:00
-- url     : https://prove2.me/theorems/7815b36a-411f-427d-824a-1598c03f4e04
-- title:
--   The tail of the Taylor series at 0 of an entire function bounded by M on the ball of radius R is at most M (r/R)^T / (1 − r/R) on the ball of radius r
-- statement:
--   Let $E$ be a complex normed space, let $G : E \to \mathbb{C}$ be analytic at every point, with $|G| \le M$ on the closed ball of radius $R$ about $0$, and let $0 < r < R$. For every $z \in E$ with $\|z\| \le r$ and every $T \in \mathbb{N}$,
--
--   $$\Bigl|G(z) - \sum_{k < T}\frac{1}{k!}\,D^kG(0)(z, \dots, z)\Bigr| \le \frac{M\,(r/R)^{T}}{1 - r/R},$$
--
--   where $D^kG$ is the $k$-th Fréchet derivative.
--
--   In the proof of Proposition 4.10 (`Transcendence.siegel_small_values_of_count`) it bounds the tail of the Taylor expansion at the origin; on $\mathbb{C}^n$ with the sup norm, the balls are polydiscs.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None: the bound for the tail in the proof of Lemma 4.13 of Waldschmidt's book (pp. 134–135), with the factor $1/(1 - r/R)$ in place of the book's $1 + \sqrt{T}$. The book bounds the tail by Schwarz's lemma and Parseval's formula; here Cauchy's inequality on the line through $z$ bounds each term, and the terms are summed as a geometric series. The contribution of this node is the formal proof.
-- source:
--   The tail bound in the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Lemma 4.13 (pp. 134–135), by Cauchy's inequality in place of Schwarz's lemma and Parseval's formula. Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **The tail of a Taylor series** (Waldschmidt, *Diophantine Approximation on Linear Algebraic
Groups*, the tail half of Lemma 4.13, with Cauchy's inequality in place of Schwarz's lemma). Let `G` be an
entire function on a complex normed space `E`, bounded by `M` on the closed ball of radius `R`, and let
`0 < r < R`. For `‖z‖ ≤ r`, the Taylor polynomial of order `< T` of `G` at `0`, whose `k`-th term is
`D^k G(0)(z, …, z) / k!`, approximates `G z` within `M (r/R)^T / (1 - r/R)`. -/
theorem taylor_tail_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {G : E → ℂ}
    (hG : AnalyticOnNhd ℂ G Set.univ) {r R M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hM : ∀ x ∈ Metric.closedBall (0 : E) R, ‖G x‖ ≤ M) {z : E} (hz : ‖z‖ ≤ r) (T : ℕ) :
    ‖G z - ∑ k ∈ Finset.range T, (k.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ k G 0 (fun _ => z)‖ ≤
      M * (r / R) ^ T / (1 - r / R) := by
  sorry

end Transcendence
