-- Prove2me | Theorems.Thm_SemisimpleQFT_corollary_4_21
-- name    : SemisimpleQFT.corollary_4_21
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-19T15:12:17.522775+00:00
-- url     : https://prove2.me/theorems/2aaa6a8a-52ec-4426-a5ae-4d72e0d8f577
-- title:
--   Corollary 4.21: $\langle D,E\rangle^{\mathrm{op}}_{\mathbf S}=d^{\,\mathrm{cc}(D\vee E)}$
-- statement:
--   For any two partition diagrams $D,E$ with $n$ columns and any $d\in\mathbb{Z}_{\ge0}$, the Schur inner product $\langle D,E\rangle^{\mathrm{op}}_{\mathbf S}=\mathrm{Tr}(\mathbf S(D)^\dagger\mathbf S(E))$ equals
--   $$\langle D,E\rangle^{\mathrm{op}}_{\mathbf S}=d^{\,\mathrm{cc}(D\vee E)},$$
--   where $D\vee E$ is the join of the two set partitions and $\mathrm{cc}$ counts blocks.
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, p. 28, Lemma 4.20 and Corollary 4.21, Eq. (4.14)

import Definitions.Def_SemisimpleQFT_Diagram

open scoped BigOperators ComplexConjugate

namespace SemisimpleQFT

theorem corollary_4_21 {n : ℕ} (d : ℕ) (D E : Diagram n) :
    Matrix.trace ((schurDiagram d D).conjTranspose * schurDiagram d E) =
      (d : ℂ) ^ cc (join D E) := by sorry

end SemisimpleQFT
