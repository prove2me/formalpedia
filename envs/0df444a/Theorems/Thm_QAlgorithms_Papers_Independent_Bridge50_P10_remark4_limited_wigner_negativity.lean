-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P10_remark4_limited_wigner_negativity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P10.remark4_limited_wigner_negativity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:22:35.314797+00:00
-- url     : https://prove2.me/theorems/1138b625-33a1-4f82-8d22-f88ce590e152
-- title:
--   Bounded Wigner negativity bounds a binary measurement bias
-- statement:
--   Let $m$ be a nonnegative integer and let $\rho_0,\rho_1$ be arbitrary positive trace-class operators of trace one on the completed $m$-mode oscillator Hilbert space. Use $\hbar=1$, ordinary phase-space Lebesgue measure $dz=d^m x\,d^m p$, and $W_I=(2\pi)^{-m}$. Let $0\le M\le I$ be a bounded binary effect with its actual bounded Wigner response $F=(2\pi)^mW_M$. Suppose $B\ge0$ and $|2F(z)-1|\le B$ for every phase-space point $z$. Writing $W_i=W_{\rho_i}$, one has
--
--   $$
--   \operatorname{Tr}[(\rho_0-\rho_1)M]\le \frac B2\int |W_0(z)-W_1(z)|\,dz.
--   $$
--
--   The integral takes values in $[0,+\infty]$. If $B>0$ and it is infinite, the bound is trivial. If $B=0$, the response is constant and the left side is zero, including when the integral is infinite. No Wigner positivity or finite-energy hypothesis on the states is imposed. This bounds the equal-prior discrimination bias even for measurements with bounded Wigner negativity.
--
--   **Formalization Note** The nonnegative right side permits the equivalent positive-part embedding of the real left side into the extended nonnegative reals. The actual response is defined by weak trace pairing on all self-adjoint trace-class tests with integrable Wigner functions.
-- source:
--   Bosonic data hiding: power of linear vs non-linear optics, arXiv:2102.01622v1, PDF p. 5, Remark 4, (23)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P10

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Bridge50.P10

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeOperator PhaseVector FockWeylSystem numberBasis numberKet)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass operatorTrace State)

open QAlgorithms.Papers.Independent.Support50.P20 (IsBinaryEffect)

/-- Remark 4, arXiv:2102.01622v1, PDF p.5, (23).
No Wigner positivity, finite energy, or L1 assumption on the states is added.
The positive-part embedding expresses exactly the source's one-sided bound,
since its right side is nonnegative. In particular 0 times infinity is 0:
B=0 is the genuine constant-response effect, not a totalized integral trick. -/
theorem remark4_limited_wigner_negativity {m : ℕ} (W : FockWeylSystem m)
    (rho0 rho1 : State (numberBasis m)) (M : ModeOperator m)
    (hM : IsBinaryEffect M) (F : PhaseVector m → ℝ)
    (hF : HasBoundedResponse W M F) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z, |2 * F z - 1| ≤ B) :
    ENNReal.ofReal
      ((operatorTrace (numberBasis m) ((rho0.val.val - rho1.val.val).comp M)).re) ≤
      ENNReal.ofReal (B / 2) * wignerL1 W (rho0.val.val - rho1.val.val) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P10

end
