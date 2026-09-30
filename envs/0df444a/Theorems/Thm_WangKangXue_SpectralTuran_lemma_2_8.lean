-- Prove2me | Theorems.Thm_WangKangXue_SpectralTuran_lemma_2_8
-- name    : WangKangXue.SpectralTuran.lemma_2_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T14:26:00.228272+00:00
-- url     : https://prove2.me/theorems/a4187904-c187-4387-9385-bf6cf61c140e
-- title:
--   Lemma 2.8 — |A_1 ∩ ⋯ ∩ A_p| ≥ Σ|A_i| − (p − 1)|A_1 ∪ ⋯ ∪ A_p|
-- statement:
--   Let $p \ge 1$ and let $A_1, \dots, A_p$ be finite sets. Then
--   $$
--   |A_1 \cap \dots \cap A_p| \ \ge\ \sum_{i=1}^p |A_i| - (p-1)\,\Big|\bigcup_{i=1}^p A_i\Big| .
--   $$
--
--   This elementary counting inequality is how the paper finds many common neighbours of a set of high-degree vertices inside one part, the step behind Lemmas 3.4–3.8.
--
--   **Formalization Note** The inequality is stated over $\mathbb Z$. The hypothesis $p \ge 1$ is implicit on the page (at $p = 0$ the empty intersection is not a finite set).
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, p. 3, Lemma 2.8 (from Cioabă, Feng, Tait, Zhang)

import Mathlib

namespace WangKangXue.SpectralTuran

open Classical

/-- **Lemma 2.8** (Wang–Kang–Xue, arXiv:2203.10831v1, p. 3; from Cioabă et al.). For finite sets
`A_1, …, A_p` (`p ≥ 1`),
`|A_1 ∩ ⋯ ∩ A_p| ≥ ∑_i |A_i| − (p − 1) |A_1 ∪ ⋯ ∪ A_p|`. -/
theorem lemma_2_8 {α : Type*} [DecidableEq α] (p : ℕ) (hp : 1 ≤ p) (A : Fin p → Finset α) :
    ((Finset.univ.inf' ⟨⟨0, hp⟩, Finset.mem_univ _⟩ A).card : ℤ) ≥
      ∑ i, ((A i).card : ℤ) - ((p : ℤ) - 1) * ((Finset.univ.biUnion A).card : ℤ) := by sorry

end WangKangXue.SpectralTuran
