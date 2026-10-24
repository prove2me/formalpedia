-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_depolarizing_necessary_42
-- name    : QAlgorithms.Papers.Independent.Support50.P04.depolarizing_necessary_42
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:47:42.929992+00:00
-- url     : https://prove2.me/theorems/587255c3-528b-4d70-8e7a-b1db435b7617
-- title:
--   Depolarizing channel: 42 uses are necessary to exceed the displayed coherent-information value
-- statement:
--   Let $\alpha=33/400=0.0825$ and $\varepsilon=11/200=0.055$. Let $D_\alpha(\rho)=(1-\alpha)\rho+(\alpha/3)(X\rho X+Y\rho Y+Z\rho Z)$, where $X,Y,Z$ are the Pauli matrices. For every positive integer $n<42$, the maximum entanglement-transmission rate with classical post-processing satisfies $$\widehat R^{\mathrm{cpp}}_{D_\alpha}(n;\varepsilon)\le 1-h(\alpha)-\alpha\log_2 3.$$ Here $h$ is binary entropy and fidelity is squared fidelity to the normalized maximally entangled target. The right side is the explicit comparison expression in Eq.(11); no general identity between this expression and maximized coherent information is assumed. This is a necessary block-length condition, with no achievability claim at 42.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 7, §II.C, Fig.4(b) discussion

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF pp.6–7, Fig.4(b) and its discussion.
At alpha=0.0825 and epsilon=5.5%, at least 42 channel uses are necessary to
exceed the comparison value displayed in Eq.(11). The statement is only this
necessary condition: it does not assert that a code attains the bound at n=42.
The separate 738 value is explicitly based on a second-order approximation.
No numerical certification premise is added to this source claim. -/
theorem depolarizing_necessary_42 (n : ℕ) (hn : 0 < n) (hsmall : n < 42) :
    cppBoundary (QuditFidelity.depolarizingMap 2 (by norm_num) (4*(33/400)/3)) n (11/200) ≤
      ((1 - QAlgorithms.Papers.Independent.Frontier18.P07.binaryEntropyBits (33/400) -
        (33/400) * QAlgorithms.Papers.Independent.Information100.P80.log2 3 : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
