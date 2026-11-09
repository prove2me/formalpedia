-- Prove2me | Theorems.Thm_PersistQMem_proposition_6_5
-- name    : PersistQMem.proposition_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:50:55.054061+00:00
-- url     : https://prove2.me/theorems/21c15c5a-b218-46bd-8add-5c07d963469c
-- title:
--   Proposition 6.5 — one-copy prior-average bound $\sum_j\frac{p_j}2\sum_{z=\pm1}d_{j,z}(A,H_{j,z})\le c_{\alpha,\theta}B_K\operatorname{Tr}A$
-- statement:
--   Fix the data of Definition 2.1, $0<\theta<1$, $\alpha>1$, and a complete refined instrument with entering memory $\mathbb C^r$, $r\le K$, and output blocks $k_a\le K$. For any positive entering memory matrix $A$ and any collection of label-dependent recorded Hermitian contractions $H_{j,z}$,
--   $$\sum_j\frac{p_j}2\sum_{z=\pm1}d_{j,z}(A,H_{j,z})\le c_{\alpha,\theta}B_K\operatorname{Tr}A,\qquad c_{\alpha,\theta}=\frac{\alpha^2\theta^2}{4(1-\theta)(\alpha-1)}.\tag{56}$$
--
--   This is the per-copy information charge that §6.5 sums over the adaptive experiment.
--
--   Differences from the source:
--   - encoding: z ∈ {−1, 1} → z : Bool with zsign true = 1, zsign false = −1; reason: Lean convention; same two signs
--   - encoding: real traces Tr(·) (drift, ℓ_j, Tr A) → real parts of complex traces; reason: the traces are real for the Hermitian and positive operators involved
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), Proposition 6.5, (56), p.25 (PDF p.28); §6.2, p.19 (r ≤ K)

import Mathlib
import Definitions.Def_PersistQMem_drift

open scoped Matrix ComplexOrder

namespace PersistQMem

/-- **Proposition 6.5 (One-copy prior-average bound), p.25** (Tao, Shen, *Structural Lower Bounds
for Quantum Property Estimation with Persistent Memory*, STOC 2027 submission, manuscript of
2026-11-03, sha256 6d48ad24…, Proposition 6.5, (56), p.25). Fix the data of Definition 2.1,
`0 < θ < 1`, `α > 1` and a complete refined instrument `Φ` with entering memory `C^r`, `r ≤ K`, and
output blocks `k_a ≤ K`. For any positive entering memory matrix `A` and any collection of
label-dependent recorded Hermitian contractions `H_{j,z}`,
`Σ_j (p_j/2) Σ_{z=±1} d_{j,z}(A, H_{j,z}) ≤ c_{α,θ} B_K Tr A`, `c_{α,θ} = α²θ²/(4(1 − θ)(α − 1))`. -/
theorem proposition_6_5 {D M : ℕ} {G : Fin M → Matrix (Fin D) (Fin D) ℂ} {p : Fin M → ℝ}
    (hG : ProfileData G p) {ι : Type} [Fintype ι] {r K : ℕ} (hrK : r ≤ K)
    (Φ : FinInstrument ι r D K) (α : ℝ) (hα : 1 < α) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (A : Matrix (Fin r) (Fin r) ℂ) (hA : A.PosSemidef) (H : Fin M → Bool → RecTest Φ)
    (hH : ∀ j z, IsRecHermContraction Φ (H j z)) :
    ∑ j, p j / 2 * ∑ z : Bool, drift Φ α (rhoAlt θ (G j) z) A (H j z) ≤
      α ^ 2 * θ ^ 2 / (4 * (1 - θ) * (α - 1)) * budget G p K * A.trace.re := by sorry

end PersistQMem
