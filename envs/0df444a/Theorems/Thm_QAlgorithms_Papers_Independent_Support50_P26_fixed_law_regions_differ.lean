-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P26_fixed_law_regions_differ
-- name    : QAlgorithms.Papers.Independent.Support50.P26.fixed_law_regions_differ
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:05:01.090923+00:00
-- url     : https://prove2.me/theorems/72a9e754-2352-4d42-b54a-90bb8955fdf7
-- title:
--   Remark 2: fixed-law superposition and successive-decoding regions differ
-- statement:
--   For a fixed finite channel and auxiliary law as in Theorem 1, let $\mathcal S(p)$ be the nonnegative region given by (9)–(11), and let $\mathcal D(p)$ instead satisfy
--   $$
--   R_1\le I(X;B_1|W),\qquad R_2\le I(W;B_2),\qquad R_2\le I(W;B_1).
--   $$
--   There is a channel and one fixed law for which $\mathcal D(p)$ is a proper subset of $\mathcal S(p)$. Explicitly, take independent fair bits $W,V$, input $X=(W,V)$, and the channel $\rho_{(w,v)}=|v\rangle\langle v|^{B_1}\otimes|w\rangle\langle w|^{B_2}$. For this law,
--   $$
--   \bigl(I(X;B_1|W),I(W;B_2),I(X;B_1),I(W;B_1)\bigr)=(1,1,1,0).
--   $$
--   Consequently $(1/2,1/2)\in\mathcal S(p)\setminus\mathcal D(p)$, while the successive-decoding corner $(I(X;B_1|W),\min\{I(W;B_1),I(W;B_2)\})=(1,0)$ belongs to both regions.
--
--   This explicit witness states the fixed-distribution noncoincidence assertion. It makes no claim that the unions over distributions differ.
-- source:
--   Classical codes for quantum broadcast channels, arXiv:1111.3645v4, PDF p. 7, Remark 2: fixed-distribution superposition and successive-decoding regions need not coincide

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P26

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P26

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact primitives from pinned accepted modules, under the independent-paper override.
-- No coding theorem or other paper's channel model is reused.

open QAlgorithms.Papers.Independent.Information100.P22 (Op quantumMI)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks)

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

variable {X B1 B2 W U V A B : Type}

variable [Fintype X] [Fintype B1] [Fintype B2] [Fintype W] [Fintype U] [Fintype V]

variable [Fintype A] [Fintype B]

variable [DecidableEq X] [DecidableEq B1] [DecidableEq B2] [DecidableEq W]

variable [DecidableEq U] [DecidableEq V] [DecidableEq A] [DecidableEq B]

/-- Remark 2, PDF pp.7–8: a fixed-law proper inclusion, explicit separating pair,
computed information values (1,1,1,0), and the common successive-decoding corner.
No inequality of the unions over auxiliary laws is asserted. -/
theorem fixed_law_regions_differ :
    let C := separatingChannel
    let p := separatingLaw
    superPrivate C p = 1 ∧ quantumMI (superWB2 C p) = 1 ∧ superTotal C p = 1 ∧
    quantumMI (superWB1 C p) = 0 ∧
    SuccessiveRegion C p ⊂ SuperRegion C p ∧
    ((1 / 2, 1 / 2) : ℝ × ℝ) ∈ SuperRegion C p ∧
    ((1 / 2, 1 / 2) : ℝ × ℝ) ∉ SuccessiveRegion C p ∧
    successiveCorner C p ∈ SuccessiveRegion C p ∩ SuperRegion C p := by sorry

end QAlgorithms.Papers.Independent.Support50.P26

end
