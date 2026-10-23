-- Prove2me | Theorems.Thm_SKAlgorithm_Qudit_lemma_2
-- name    : SKAlgorithm.Qudit.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:00.180608+00:00
-- url     : https://prove2.me/theorems/608a8345-11b4-4f59-97ad-6689aae291b4
-- title:
--   Lemma 2, p. 11 — a traceless Hermitian matrix is a balanced commutator of Hermitian matrices
-- statement:
--   Let $H$ be a traceless $d \times d$ Hermitian matrix. Then there are Hermitian $d \times d$ matrices $F$ and $G$ such that
--   $$[F, G] = FG - GF = iH$$
--   and
--   $$\|F\|,\ \|G\| \le d^{1/4} \left(\frac{d - 1}{2}\right)^{1/2} \sqrt{\|H\|} .$$
--
--   The lemma lets the qudit algorithm write the generator of a gate close to the identity as a commutator of two generators, each of norm $O(\sqrt{\|H\|})$; exponentiating them gives the balanced group commutator of Eq. (33).
--
--   **Formalization Note.** Norms are operator norms (`QAlgorithms.specNorm`). The factor $((d-1)/2)^{1/2}$ is written `Real.sqrt (((d:ℝ) - 1) / 2)`; for $d \le 1$ every traceless Hermitian matrix is zero and the statement is satisfied by $F = G = 0$.
-- source:
--   Dawson and Nielsen, The Solovay-Kitaev algorithm, arXiv:quant-ph/0505030v2, p. 11, §5.2, Lemma 2, Eqs. (24)–(25)

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open scoped Matrix
open QAlgorithms

namespace SKAlgorithm.Qudit

theorem lemma_2 {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (htr : H.trace = 0) :
    ∃ F G : Matrix (Fin d) (Fin d) ℂ, F.IsHermitian ∧ G.IsHermitian ∧
      F * G - G * F = Complex.I • H ∧
      specNorm F ≤ (d : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (((d : ℝ) - 1) / 2) * Real.sqrt (specNorm H) ∧
      specNorm G ≤ (d : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (((d : ℝ) - 1) / 2) * Real.sqrt (specNorm H) := by sorry

end SKAlgorithm.Qudit
