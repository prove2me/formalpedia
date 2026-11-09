-- Prove2me | Theorems.Thm_QuarticGauss390_EigenBound_lemma_4_2
-- name    : QuarticGauss390.EigenBound.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:52.320931+00:00
-- url     : https://prove2.me/theorems/f21ba817-2ea4-4b9f-bc46-e3cafcb9556c
-- title:
--   Lemma 4.2 — $\tau[R^2]=1$ and $\|C^R\|_{\mathrm{op}}\le1/\sqrt n$ imply $\|R\|_{\mathrm{op}}\le\frac52\sqrt n$
-- statement:
--   Fix a CAR system on $n\ge2$ modes. Let $R=\sum_{|S|=4}r_Sc_S$ be homogeneous quartic with real coefficients. If
--   $$\tau[R^2]=1\qquad\text{and}\qquad\|C^R\|_{\mathrm{op}}\le\frac1{\sqrt n},$$
--   then
--   $$\|R\|_{\mathrm{op}}\le\frac52\sqrt n .$$
--
--   A quartic operator whose coefficient matrix has small spectral norm has operator norm only $O(\sqrt n)$ times its normalized Frobenius norm.
--
--   For $n=2,3$ the two hypotheses cannot hold together (since $\operatorname{Tr}[(C^R)^2]=6$ and $C^R$ has $m=\binom{2n}2<6n$ eigenvalues, $\|C^R\|_{\mathrm{op}}\ge\sqrt{6/m}>1/\sqrt n$), so the statement is vacuous there, exactly as in the source; it has content for $n\ge4$.
--
--   Differences from the source:
--   - encoding: $\|\cdot\|_{\mathrm{op}}$ → the norm of the matrix as a linear map on Euclidean space, for $C^R$ (real) and $R$ (complex); reason: the spectral norm of the source
-- source:
--   Ojas Parekh, Improved classical optimization of fermionic Hamiltonians beyond Gaussian states, STOC 2027 submission #390 (October 2026), source.pdf SHA-256 9018757e184cce1091160d8b5847294a0e6c16cc09386b1f2b6bb000f7542101, p.15, Lemma 4.2

import Mathlib
import Definitions.Def_QuarticGauss390_EigenBound_CAR
import Definitions.Def_QuarticGauss390_EigenBound_Moments
import Definitions.Def_QuarticGauss390_EigenBound_MatrixNorms

open Matrix

namespace QuarticGauss390.EigenBound

/-- Lemma 4.2, p.15: if `R` is homogeneous quartic, `τ[R²] = 1` and
`‖C^R‖_op ≤ 1/√n`, then `‖R‖_op ≤ (5/2)√n`. -/
theorem lemma_4_2 {n : ℕ} (hn : 2 ≤ n) (C : CAR n) (r : Finset (Fin (2 * n)) → ℝ)
    (hR : normTrace n (quartic C r * quartic C r) = 1)
    (hCR : opNorm (coefMatrix C (quartic C r)) ≤ 1 / Real.sqrt n) :
    opNorm (quartic C r) ≤ 5 / 2 * Real.sqrt n := by sorry

end QuarticGauss390.EigenBound
