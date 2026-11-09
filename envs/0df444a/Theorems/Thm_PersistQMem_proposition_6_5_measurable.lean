-- Prove2me | Theorems.Thm_PersistQMem_proposition_6_5_measurable
-- name    : PersistQMem.proposition_6_5_measurable
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:50:53.101108+00:00
-- url     : https://prove2.me/theorems/ce9f4de3-a64c-4bff-b069-49fc83002e4e
-- title:
--   §6.6 — Proposition 6.5 for measurable instruments
-- statement:
--   Fix the data of Definition 2.1, $0<\theta<1$, $\alpha>1$, and a measurable complete instrument with entering memory $\mathbb C^r$, $r\le K$, and retained memory $\mathbb C^K$, given by a reference measure $\mu$ and measurable Kraus fields $M_{a,l}$ with $\int\sum_lM_{a,l}^*M_{a,l}\,d\mu(a)=I_{rD}$ (68). For any positive entering memory matrix $A$ and any label-dependent bounded measurable fields $a\mapsto H_{j,z}(a)$ of Hermitian contractions,
--   $$\sum_j\frac{p_j}2\sum_{z=\pm1}d_{j,z}(A,H_{j,z})\le\frac{\alpha^2\theta^2}{4(1-\theta)(\alpha-1)}B_K\operatorname{Tr}A,$$
--   where the drift (44) integrates over records with respect to $\mu$ instead of summing over outcomes.
--
--   This is the local charge of the continuous-outcome proof of Theorem 2.2.
--
--   Differences from the source:
--   - encoding: a measurable instrument (Choi measure, Hilbert direct integrals) → the Kraus-density form (μ, M_{a,l}) of (68), with outputs in C^K; reason: every measurable complete instrument has this form (milestone eq_67_68_kraus_density), and every such density defines one
--   - encoding: bounded measurable recorded Hermitian contraction fields → fields that are Hermitian contractions at every record and entrywise measurable; reason: a Hermitian contraction is bounded by 1
--   - encoding: z ∈ {−1, 1} → z : Bool with zsign true = 1, zsign false = −1; reason: Lean convention; same two signs
--   - encoding: real traces Tr(·) (drift, ℓ_j, Tr A) → real parts of complex traces; reason: the traces are real for the Hermitian and positive operators involved
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), §6.6, pp.27–28 (PDF pp.30–31), with Proposition 6.5, (56), p.25

import Mathlib
import Definitions.Def_PersistQMem_KrausDensityInstrument

open scoped Matrix ComplexOrder
open MeasureTheory

namespace PersistQMem

/-- **§6.6, pp.27–28: Proposition 6.5 for measurable instruments** (Tao, Shen, *Structural Lower
Bounds for Quantum Property Estimation with Persistent Memory*, STOC 2027 submission, manuscript of
2026-11-03, sha256 6d48ad24…, §6.6, pp.27–28, with (56), p.25). Fix the data of Definition 2.1,
`0 < θ < 1`, `α > 1`, and a measurable complete instrument with entering memory `C^r`, `r ≤ K`, and
retained memory `C^K`, in Kraus-density form `(μ, M_{a,l})` (68). For any positive entering memory
matrix `A` and any label-dependent bounded measurable recorded Hermitian contraction fields
`H_{j,z}(a)`, `Σ_j (p_j/2) Σ_{z=±1} d_{j,z}(A, H_{j,z}) ≤ c_{α,θ} B_K Tr A`, where the drift (44)
integrates over records instead of summing. -/
theorem proposition_6_5_measurable {D M : ℕ} {G : Fin M → Matrix (Fin D) (Fin D) ℂ}
    {p : Fin M → ℝ} (hG : ProfileData G p) {X : Type} [MeasurableSpace X] {μ : Measure X}
    {L : Type} [Fintype L] {r K : ℕ} (hrK : r ≤ K) (Φ : KrausDensityInstrument X μ L r D K)
    (α : ℝ) (hα : 1 < α) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (A : Matrix (Fin r) (Fin r) ℂ) (hA : A.PosSemidef)
    (H : Fin M → Bool → X → Matrix (Fin K) (Fin K) ℂ)
    (hH : ∀ j z a, IsHermContraction (H j z a))
    (hHm : ∀ j z o o', Measurable fun a => H j z a o o') :
    ∑ j, p j / 2 * ∑ z : Bool, densDrift Φ α (rhoAlt θ (G j) z) A (H j z) ≤
      α ^ 2 * θ ^ 2 / (4 * (1 - θ) * (α - 1)) * budget G p K * A.trace.re := by sorry

end PersistQMem
