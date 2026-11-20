-- Prove2me | Theorems.Thm_SemisimpleQFT_lemma_4_4
-- name    : SemisimpleQFT.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-19T15:11:38.780858+00:00
-- url     : https://prove2.me/theorems/d6c22c44-6108-400c-9aae-d4b572f37774
-- title:
--   Lemma 4.4: $\mathrm{pn}(D_1D_2)\le\min\{\mathrm{pn}(D_1),\mathrm{pn}(D_2)\}$
-- statement:
--   For all partition diagrams $D_1$ and $D_2$ with $n$ columns, the propagating number of the diagram of the product satisfies
--   $$\mathrm{pn}(D_1D_2)\le\min\{\mathrm{pn}(D_1),\mathrm{pn}(D_2)\}.$$
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, p. 23, Lemma 4.4

import Definitions.Def_SemisimpleQFT_Diagram

open scoped BigOperators ComplexConjugate

namespace SemisimpleQFT

theorem lemma_4_4 {n : ℕ} (D₁ D₂ : Diagram n) :
    pn (comp D₁ D₂) ≤ min (pn D₁) (pn D₂) := by sorry

end SemisimpleQFT
