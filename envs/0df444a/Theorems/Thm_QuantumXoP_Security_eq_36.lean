-- Prove2me | Theorems.Thm_QuantumXoP_Security_eq_36
-- name    : QuantumXoP.Security.eq_36
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:07:34.466282+00:00
-- url     : https://prove2.me/theorems/699d4526-3cad-42f5-bb98-c2641b73e312
-- title:
--   §7.3, Eq. (36) — $\|B^\dagger|\Xi\rangle\|^2\le\frac4N\langle\Xi|(D_{\mathrm{cnt}}+\mathrm{Col}_{\mathrm{cnt}})|\Xi\rangle$
-- statement:
--   Let $|\Xi\rangle$ be a joint algorithm–database state whose database registers are supported on $\mathrm{span}\{|\hat f\rangle:f\in F\}$. Then
--   $$\|B^\dagger|\Xi\rangle\|^2\le\frac4N\,\langle\Xi|\,(D_{\mathrm{cnt}}+\mathrm{Col}_{\mathrm{cnt}})\,|\Xi\rangle .$$
--
--   It is the operator bound used with Lemma 7.4 in the proof of Lemma 7.2; the paper displays it as Eq. (36) and proves it in Appendix C.
--
--   **Formalization Note** "Supported on the span" is written $|\Xi\rangle=\sum_f|\varphi_f\rangle\otimes|\hat f\rangle$ for some vectors $\varphi_f$ of the algorithm registers; the state need not be normalized, since both sides scale alike.
--
--   Differences from the source:
--   - generalization: n is a fixed positive integer (§2, p. 8) → every n : ℕ, including n = 0; reason: the case n = 0 is one extra instance; the statement specializes to every n ≥ 1
--   - generalization: a joint algorithm-database state supported on the indicated span → an arbitrary vector supported on that span, with no norm restriction; reason: both sides are homogeneous of degree two; scaling a nonzero vector to unit norm recovers the source, and the zero vector satisfies both sides with equality
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 39 (PDF p. 41), Eq. (36) (proof App. C, p. 47)

import Mathlib
import Definitions.Def_QuantumXoP_Security_Compressed

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- §7.3, Eq. (36) (p. 39; proof App. C, p. 47): every joint algorithm–database state `|Ξ⟩`
whose database registers are supported on `span{|f^⟩ : f ∈ F}` satisfies
`‖B† |Ξ⟩‖² ≤ (4/N) ⟨Ξ| (D_cnt + Col_cnt) |Ξ⟩`. -/
theorem eq_36 {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (Ξ : EuclideanSpace ℂ (Reg n W × DB n)) (hΞ : InFhatSpan Ξ) :
    ‖act (bOp n W).conjTranspose Ξ‖ ^ 2 ≤
      4 / bigN n * (expectDiag Ξ dcnt + expectDiag Ξ colcnt) := by sorry

end QuantumXoP.Security
