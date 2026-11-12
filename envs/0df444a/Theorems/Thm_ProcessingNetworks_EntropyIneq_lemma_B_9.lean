-- Prove2me | Theorems.Thm_ProcessingNetworks_EntropyIneq_lemma_B_9
-- name    : ProcessingNetworks.EntropyIneq.lemma_B_9
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T13:29:42.187565+00:00
-- url     : https://prove2.me/theorems/7ee62f31-62e4-43de-88d7-d3b680e48b01
-- title:
--   Lemma B.9 — every class is reachable from an input class
-- statement:
--   Throughout, $I\ge1$ is an integer, $\mathcal I=\{1,\dots,I\}$ is the set of classes, $\lambda\in\mathbb R^I_+$ is the vector of external arrival rates and $P$ is a non-negative $I\times I$ routing matrix with spectral radius $\rho(P)<1$; $P_{i0}:=1-\sum_{j\in\mathcal I}P_{ij}$, $\mathcal I_+=\mathcal I\cup\{0\}$, $\alpha:=(I-P')^{-1}\lambda$ is assumed positive and $\alpha_0:=1$ (Section B.4, (B.13)–(B.17)). Let $\mathcal I_0:=\{i\in\mathcal I:\lambda_i>0\}$ be the set of input classes (B.18).
--
--   For each class $i\in\mathcal I$ there exist an integer $p\ge0$ and classes $i_0,i_1,\dots,i_p$ such that
--
--   $$
--   i_0\in\mathcal I_0,\qquad P_{i_ki_{k+1}}>0\ \ (k=0,1,\dots,p-1),\qquad i_p=i .
--   $$
--
--   In words, $\mathcal I_0$ is not empty and every class is reachable from an input class along routes of positive probability.
--
--   **Formalization Note** The classes $i_0,\dots,i_p$ are a map from $\{0,\dots,p\}$ to the classes; $p=0$ is allowed.
--
--   Differences from the source:
--
--   - encoding: the chain i₀, …, i_p of classes in {1, …, I} → a map c : Fin (p + 1) → Fin I with c 0 = i₀ and c (Fin.last p) = i_p; reason: 0-based class indices; same chains
--   - encoding: ρ(P) < 1, ρ the largest modulus of an eigenvalue → RobustToDynamics.specRadius P < 1, the supremum of the moduli of the points of the spectrum of P over ℂ; reason: that spectrum is the set of complex eigenvalues, a finite nonempty set for I ≥ 1, so the supremum is the maximum
--   - encoding: α := (I − P′)⁻¹λ → traffic lam P, defined with Matrix.inv; reason: ρ(P) < 1 makes I − P′ invertible (Theorem F.1), so Matrix.inv is the true inverse
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix B §B.4, Lemma B.9, eq. (B.19), p.269 (PDF 285)

import Mathlib
import Definitions.Def_ProcessingNetworks_EntropyIneq_SectionB4Assumptions

namespace ProcessingNetworks.EntropyIneq

/-- **Lemma B.9** (Dai & Harrison, *Processing Networks*, pre-publication draft 2020-4-2,
spnbook.org, Appendix B §B.4, Lemma B.9, eq. (B.19), p.269 (PDF 285)). Under the standing
assumptions of Section B.4, for each class `i ∈ 𝓘` there exist an integer `p ≥ 0` and classes
`i₀, i₁, …, i_p` such that `i₀ ∈ 𝓘₀` (that is, `λ_{i₀} > 0`, (B.18)),
`P_{i_k i_{k+1}} > 0` for `k = 0, 1, …, p − 1`, and `i_p = i`.

**Formalization Note** The classes `i₀, …, i_p` are a map `c : Fin (p + 1) → Fin I`; `c 0 = i₀`,
`c (Fin.last p) = i_p`, and `k : Fin p` ranges over `0, …, p − 1` with `c k.castSucc = i_k`,
`c k.succ = i_{k+1}`. The input classes `𝓘₀ = {i : λᵢ > 0}` (B.18) are written out. -/
theorem lemma_B_9 {I : ℕ} (lam : Fin I → ℝ) (P : Matrix (Fin I) (Fin I) ℝ)
    (hB4 : SectionB4Assumptions lam P) (i : Fin I) :
    ∃ p : ℕ, ∃ c : Fin (p + 1) → Fin I,
      0 < lam (c 0) ∧ (∀ k : Fin p, 0 < P (c k.castSucc) (c k.succ)) ∧ c (Fin.last p) = i := by sorry

end ProcessingNetworks.EntropyIneq
