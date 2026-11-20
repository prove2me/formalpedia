-- Prove2me | Theorems.Thm_SemisimpleQFT_lemma_4_22
-- name    : SemisimpleQFT.lemma_4_22
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-19T15:12:51.238846+00:00
-- url     : https://prove2.me/theorems/9de50656-3fd9-4826-b1c6-c378a6253f03
-- title:
--   Lemma 4.22: $2\,\mathrm{cc}(D\vee E)\le\mathrm{cc}(D)+\mathrm{cc}(E)$ with equality iff $D=E$
-- statement:
--   For any two partition diagrams $D$ and $E$ with $n$ columns,
--   $$2\cdot\mathrm{cc}(D\vee E)\le\mathrm{cc}(D)+\mathrm{cc}(E),$$
--   with equality if and only if $D=E$. Hence, for $d\ge1$ and distinct scaled diagrams $a=d^{(n-\mathrm{cc}(D))/2}D$, $b=d^{(n-\mathrm{cc}(E))/2}E$ of the computational basis,
--   $$|\langle a,b\rangle^{\mathrm{op}}_{\mathbf S}|\le d^{\,n-1/2}.$$
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, p. 28, Lemma 4.22

import Definitions.Def_SemisimpleQFT_Diagram

open scoped BigOperators ComplexConjugate

namespace SemisimpleQFT

theorem lemma_4_22 {n : ℕ} (D E : Diagram n) :
    2 * cc (join D E) ≤ cc D + cc E ∧
    (2 * cc (join D E) = cc D + cc E ↔ D = E) ∧
    (∀ d : ℕ, 1 ≤ d → D ≠ E →
      ‖((scale d D : ℝ) : ℂ) * ((scale d E : ℝ) : ℂ) *
          Matrix.trace ((schurDiagram d D).conjTranspose * schurDiagram d E)‖ ≤
        (d : ℝ) ^ ((n : ℝ) - 1 / 2)) := by sorry

end SemisimpleQFT
