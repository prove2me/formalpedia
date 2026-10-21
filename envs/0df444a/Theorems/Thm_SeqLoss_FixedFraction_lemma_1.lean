-- Prove2me | Theorems.Thm_SeqLoss_FixedFraction_lemma_1
-- name    : SeqLoss.FixedFraction.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:00.185843+00:00
-- url     : https://prove2.me/theorems/05751e4d-6987-43b3-af71-0d798664e40a
-- title:
--   Lemma 1, p. 21 — an additive rule is scale invariant: $\varphi(\alpha\ell)=\alpha\,\varphi(\ell)$ for $\alpha\ge 0$
-- statement:
--   Let $\varphi$ be a (continuous) rule satisfying additivity. Then for each $n$, each loss vector $\ell\in L^n$ and each $\alpha\ge 0$,
--   $$\varphi(\alpha\cdot\ell)=\varphi(\alpha\ell_1,\dots,\alpha\ell_n)=(\alpha\varphi_1(\ell),\dots,\alpha\varphi_n(\ell))=\alpha\cdot\varphi(\ell).$$
--
--   Scale invariance turns additivity into linearity on the cone $L^n$; it is the step that reduces every problem to the elementary problems in Proposition 1.
--
--   **Formalization Note.** The hypothesis `IsRule φ` carries the paper's standing continuity assumption (footnote 3), on which the case of irrational $\alpha$ relies.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses: Automated Conflict Resolution Through Smart Contracts, accepted manuscript (2023), Management Science 70(3) 1773–1786, doi:10.1287/mnsc.2023.4772, Appendix A, p. 21, Lemma 1

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_FixedFraction_Axioms

namespace SeqLoss.FixedFraction

theorem lemma_1 (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hadd : Additive φ) (n : ℕ) (ℓ : Fin n → ℝ) (hℓ : IsLoss ℓ) (α : ℝ) (hα : 0 ≤ α) :
    φ n (α • ℓ) = α • φ n ℓ := by sorry

end SeqLoss.FixedFraction
