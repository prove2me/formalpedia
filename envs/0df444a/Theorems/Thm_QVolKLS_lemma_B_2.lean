-- Prove2me | Theorems.Thm_QVolKLS_lemma_B_2
-- name    : QVolKLS.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:40:39.700421+00:00
-- url     : https://prove2.me/theorems/6cc60b63-5535-4087-9c12-259709d58e12
-- title:
--   Lemma B.2 — quadrature error: $|Z_\Lambda-Z|\le\varepsilon_{\mathrm{quad}}Z$ and $d_{\mathrm{TV}}(\tilde\pi_\Lambda,\pi)\le\varepsilon_{\mathrm{quad}}$
-- statement:
--   Let $K\subset\mathbb R^D$ be a convex body with $B(x_c,r_0)\subseteq K\subseteq B(x_c,R_0)$, $\Lambda=h\mathbb Z^D$, $Q_\Lambda=h[-\tfrac12,\tfrac12)^D$, and $\varrho_\Lambda$ a cell-radius bound with $h\sqrt D/2\le\varrho_\Lambda\le h\sqrt D$. There is a constant $C>0$ such that the following holds. Suppose $\varrho_\Lambda\le r_0/4$ and
--   $$
--   \varepsilon_{\mathrm{quad}}=C\Big(\frac{(D+\|b\|_2R_0)\varrho_\Lambda}{r_0}+\|b\|_2\varrho_\Lambda\Big)\le1 .
--   \tag{66}
--   $$
--   Then
--   $$
--   |Z_\Lambda-Z|\le\varepsilon_{\mathrm{quad}}Z,\tag{67}
--   $$
--   and, for $X_\Lambda\sim\pi_\Lambda$ and $E$ an independent uniform point of $Q_\Lambda$, the law $\tilde\pi_\Lambda$ of $X_\Lambda+E$ satisfies
--   $$
--   d_{\mathrm{TV}}(\tilde\pi_\Lambda,\pi)\le\varepsilon_{\mathrm{quad}} .\tag{68}
--   $$
--   These bounds hold simultaneously for finitely many tilts when $\|b\|_2$ is replaced in (66) by their largest norm.
--
--   Here $Z=\int_Ke^{-\langle b,x\rangle}dx$, $\pi$ is the log-affine law, $Z_\Lambda=h^D\sum_{z\in K\cap\Lambda}e^{-\langle b,z\rangle}$ and $\pi_\Lambda$ the lattice law. This is the discretization estimate behind every lattice normalization constant of the algorithm.
--
--   **Formalization Note** Stated for a family $b_1,\dots,b_k$ and any common bound $\beta\ge\|b_j\|_2$ in (66); a single tilt is $k=1$, $\beta=\|b\|_2$.
--
--   Differences from the source:
--   - generalization: ‖b‖₂ in (66), or the largest norm of finitely many tilts → any common upper bound β ≥ ‖b_j‖₂ of a finite family; reason: ε_quad is increasing in β; β = ‖b‖₂ (one tilt) and β = max_j ‖b_j‖₂ are the printed cases
--   - generalization: a dyadic spacing h and a known dyadic cell-radius bound ϱ_Λ → any h > 0 and any ϱ_Λ with h√D/2 ≤ ϱ_Λ ≤ h√D; reason: the lemma does not use dyadicity
--   - encoding: d_TV(π̃_Λ, π) = sup_A |π̃_Λ(A) − π(A)| → measTV over measurable A, with π̃_Λ = Σ_z π_Λ(z)·h^{−D}·Lebesgue on z + Q_Λ; reason: the law of X_Λ + E
--   - reading: B(x₀, r) ⊆ K ⊆ B(x₀, R) with B(x, r) not specified open or closed → open inner ball, closed outer ball; reason: the stronger of the readings: an open inner ball and a closed outer ball admit the most bodies
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), Lemma B.2, p.63 (setting (64)–(65), p.62)

import Definitions.Def_QVolKLS_logAffineZ

set_option autoImplicit false

namespace QVolKLS

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **Lemma B.2 (Quadrature error)**,
p.63, in the setting (64)–(65) of App. B.2, p.62: `K ⊂ ℝ^D` a convex body with
`B(x_c, r₀) ⊆ K ⊆ B(x_c, R₀)`, `Λ = hℤ^D`, `Q_Λ = h[−1/2, 1/2)^D`, a cell-radius bound
`h√D/2 ≤ ϱ_Λ ≤ h√D`, `Z_Λ = h^D Σ_{z ∈ K ∩ Λ} e^{−⟨b,z⟩}`, `π_Λ(z) = h^D e^{−⟨b,z⟩}/Z_Λ`.

There is a constant `C > 0` such that: if `ϱ_Λ ≤ r₀/4` and
`ε_quad = C((D + ‖b‖₂R₀)ϱ_Λ/r₀ + ‖b‖₂ϱ_Λ) ≤ 1` (66), then `|Z_Λ − Z| ≤ ε_quad Z` (67), and the law `π̃_Λ`
of `X_Λ + E` (`X_Λ ∼ π_Λ`, `E` uniform on `Q_Λ`, independent) satisfies `d_TV(π̃_Λ, π) ≤ ε_quad` (68).
These bounds hold simultaneously for finitely many tilts when `‖b‖₂` is replaced in (66) by their
largest norm.

**Formalization Note.** The statement is for a finite family of tilts `b_1, …, b_k` and any common
bound `β ≥ ‖b_j‖₂` used in place of `‖b‖₂` in (66); a single tilt is `k = 1`, `β = ‖b‖₂`, and the
paper's last sentence is `β = max_j ‖b_j‖₂`. `C` is absolute ("a sufficiently large constant"). The
inner ball is open and the outer ball closed. The spacing `h` and the bound `ϱ_Λ` need not be dyadic
(the lemma does not use it). -/
theorem lemma_B_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D : ℕ), 1 ≤ D → ∀ (K : Set (Euc D)) (xc : Euc D) (r0 R0 : ℝ),
        IsConvexBody K → 0 < r0 → Metric.ball xc r0 ⊆ K → K ⊆ Metric.closedBall xc R0 →
        ∀ (k : ℕ) (bs : Fin k → Euc D) (β : ℝ), (∀ j, ‖bs j‖ ≤ β) →
        ∀ (h ϱ : ℝ), 0 < h → h * Real.sqrt D / 2 ≤ ϱ → ϱ ≤ h * Real.sqrt D → ϱ ≤ r0 / 4 →
          C * (((D : ℝ) + β * R0) * ϱ / r0 + β * ϱ) ≤ 1 →
          ∀ j,
            |latticeZ K h (bs j) - logAffineZ K (bs j)| ≤
                C * (((D : ℝ) + β * R0) * ϱ / r0 + β * ϱ) * logAffineZ K (bs j) ∧
            measTV (smoothedLatticeMeasure K h (bs j)) (logAffineMeasure K (bs j)) ≤
                C * (((D : ℝ) + β * R0) * ϱ / r0 + β * ϱ) := by sorry

end QVolKLS
