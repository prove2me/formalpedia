-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_lemma_5_11
-- name    : QuantumSymmetryBreaking.CycleColoring.lemma_5_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:24:08.946359+00:00
-- url     : https://prove2.me/theorems/9ed17e90-8ff8-4785-bfb8-a96aacba7b6e
-- title:
--   Lemma 5.11 — normalized traces of reduced Haar-orthogonal words vanish almost surely
-- statement:
--   Fix $s\ge1$. For each $d\ge1$ let $O^{(d)}_1,\dots,O^{(d)}_s\in O(d)$ be independent Haar-random orthogonal matrices, all defined on a common probability space (with no assumption on the joint law across different $d$). Fix $k\ge1$, indices $i_1,\dots,i_k\in[s]$ with $i_j\ne i_{j+1}$ for $j\in[k-1]$, and signs $\sigma_1,\dots,\sigma_k\in\{-1,1\}$. Then, with probability one,
--   $$
--   \frac1d\operatorname{Tr}\Bigl((O^{(d)}_{i_1})^{\sigma_1}\cdots(O^{(d)}_{i_k})^{\sigma_k}\Bigr)\longrightarrow0\qquad(d\to\infty).
--   $$
--   This consequence of the asymptotic freeness theorem of Collins and Śniady (2006, Theorem 5.2) is what makes the representations of Lemma 5.7 asymptotically orthogonal.
--
--   Differences from the source:
--   - encoding: independent Haar-random $O^{(d)}_1,\dots,O^{(d)}_s$ on a common probability space → measurable maps $\omega\mapsto(O^{(d)}_i(\omega))_i$ into $O(d)^s$ whose law is the product of $s$ normalized Haar measures (published `haarO`), for each $d\ge1$; reason: this is the definition of independent Haar-distributed random matrices; nothing is assumed across different $d$
--   - encoding: $d\ge1$ in the limit → the sequence indexed by all $d\in\mathbb N$; reason: the value at $d=0$ does not affect the limit
--   - encoding: signs in $\{-1,1\}$ and $[s]$ → signs in $\mathbb Z^\times$ (group power in $O(d)$), indices in `Fin s`; reason: $\mathbb Z^\times=\{1,-1\}$; relabelling only
-- source:
--   Flin, Li, Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), source.pdf SHA-256 121c1ecfd6ed3365b5424f6f5978549d12510d800fb87cb8d2f5e110600a542e, Lemma 5.11, p.26 (PDF p.29)

import Mathlib
import Definitions.Def_FourierRankQLB_Od
import Definitions.Def_FourierRankQLB_haarO

open MeasureTheory Filter Topology FourierRankQLB

namespace QuantumSymmetryBreaking.CycleColoring

/-- Lemma 5.11 (corollary of Collins–Śniady 2006, Theorem 5.2), Flin, Li, Suomela, *Quantum Advantage for Distributed Symmetry Breaking*, STOC 2027 submission #863 (October 2026), p.26 (PDF p.29).
Fix `s ≥ 1`. For each `d ≥ 1` let `O_1^{(d)}, …, O_s^{(d)} ∈ O(d)` be independent Haar-random matrices,
all defined on one probability space. For fixed `k ≥ 1`, indices `i_1, …, i_k ∈ [s]` with
`i_j ≠ i_{j+1}` and signs `σ_1, …, σ_k ∈ {−1, 1}`, almost surely
`(1/d) Tr((O_{i_1}^{(d)})^{σ_1} ⋯ (O_{i_k}^{(d)})^{σ_k}) → 0` as `d → ∞`. -/
theorem lemma_5_11 (s : ℕ) (hs : 1 ≤ s) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (O : (d : ℕ) → Ω → Fin s → Od d)
    (hO_meas : ∀ d : ℕ, 1 ≤ d → Measurable (O d))
    (hO_law : ∀ d : ℕ, 1 ≤ d → P.map (O d) = Measure.pi fun _ : Fin s => haarO d)
    (k : ℕ) (hk : 1 ≤ k) (idx : Fin k → Fin s)
    (hidx : ∀ (j : Fin k) (hj : j.val + 1 < k), idx j ≠ idx ⟨j.val + 1, hj⟩)
    (σ : Fin k → ℤˣ) :
    ∀ᵐ ω ∂P, Tendsto (fun d : ℕ => (1 / (d : ℝ)) *
      Matrix.trace (List.ofFn fun j : Fin k =>
        ((O d ω (idx j) ^ ((σ j : ℤˣ) : ℤ) : Od d) : Matrix (Fin d) (Fin d) ℝ)).prod)
      atTop (𝓝 0) := by sorry

end QuantumSymmetryBreaking.CycleColoring
