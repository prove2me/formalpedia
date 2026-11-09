-- Prove2me | Theorems.Thm_PreprocOWS_sec5_1_trace_moment
-- name    : PreprocOWS.sec5_1_trace_moment
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:24:12.004205+00:00
-- url     : https://prove2.me/theorems/26950413-78c1-42b1-af17-b1d2603d5ae1
-- title:
--   §5.1 trace-moment display: $\mathbb E\|Y\|\le(\mathbb E\|Y\|^{2t})^{1/2t}\le(\mathbb E\,\mathrm{Tr}\,Y^{2t})^{1/2t}$
-- statement:
--   Let $(Y_i)_{i\in I}$ be a family of Hermitian complex $d\times d$ matrices indexed by a nonempty finite set $I$, and let $\mathbb E_i$ be the uniform average over $I$. For every integer $t\ge1$,
--   $$
--   \mathbb E_i\|Y_i\|\le\big(\mathbb E_i\|Y_i\|^{2t}\big)^{1/2t}\le\big(\mathbb E_i\,\mathrm{Tr}(Y_i^{2t})\big)^{1/2t},
--   $$
--   where $\|\cdot\|$ is the operator norm. In §5.1 this is applied to $Y_R$ with $R$ uniform over all oracles.
--
--   This is the trace moment method: it replaces the norm, which is hard to average, by a trace moment, which the compressed oracle can compute.
--
--   **Formalization Note** The trace of a Hermitian matrix is real and is taken through its real part.
--
--   Differences from the source:
--   - generalization: the random matrix Y_R, R uniform over all oracles → any family of Hermitian matrices over a nonempty finite index set under the uniform average; reason: the page's statement is the case of the family R ↦ Y_R; Y_R is Hermitian (display (4))
--   - encoding: Tr(Y^{2t}) (a real number for Hermitian Y) → the real part (Matrix.trace …).re; reason: the trace of a power of a Hermitian matrix is real, so taking re changes no value
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §5.1, trace-moment display (Jensen), p.18 (PDF p.21)

import Mathlib
import Definitions.Def_PreprocOWS_Oracle
import Definitions.Def_PreprocOWS_vnormSq
open Matrix

namespace PreprocOWS

/-- **§5.1, trace-moment display (Jensen)**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), p.18 (PDF p.21): for every integer `t ≥ 1`,
`E_R‖Y_R‖ ≤ (E_R‖Y_R‖^{2t})^{1/2t} ≤ (E_R Tr(Y_R^{2t}))^{1/2t}`.

**Formalization Note.** Stated for every family `Y : ι → Matrix d d ℂ` of Hermitian matrices over a
nonempty finite index set under the uniform average `avg`; the page's `Y_R` with `R` uniform over all
oracles is the case `ι = Oracle K N`, `Y = Ymat A`. `‖·‖` is the operator norm `opNorm`, the trace is
real for Hermitian matrices and is taken through `re`. Powers `1/2t` are real powers of nonnegative
reals. -/
theorem sec5_1_trace_moment {ι d : Type*} [Fintype ι] [Nonempty ι] [Fintype d] [DecidableEq d]
    (Y : ι → Matrix d d ℂ) (hY : ∀ i, (Y i).IsHermitian) (t : ℕ) (ht : 1 ≤ t) :
    avg (fun i => opNorm (Y i)) ≤ (avg fun i => opNorm (Y i) ^ (2 * t)) ^ ((1 : ℝ) / (2 * t)) ∧
      (avg fun i => opNorm (Y i) ^ (2 * t)) ^ ((1 : ℝ) / (2 * t)) ≤
        (avg fun i => ((Y i ^ (2 * t)).trace).re) ^ ((1 : ℝ) / (2 * t)) := by sorry

end PreprocOWS
