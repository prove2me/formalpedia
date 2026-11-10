-- Prove2me | Theorems.Thm_TolProdTest_theorem_3_8_statistical
-- name    : TolProdTest.theorem_3_8_statistical
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:28:17.029996+00:00
-- url     : https://prove2.me/theorems/bc95f09d-adbf-41c1-a20e-28e3d9ffe644
-- title:
--   Theorem 3.8, proof — statistical step: the ideal Protocol 3.1 errs with probability $\le\delta/4$
-- statement:
--   Let $1\ge a>b\ge0$, $\delta\in(0,1/2)$, $n\ge1$, $d\ge2$. Run Protocol 3.1 with exact local measurements: $T$ independent trials of the $k$-copy product test on $T\cdot k$ copies of $\rho$, accepting iff the fraction of accepting trials is at least $(p_Y+p_N)/2$, with the parameters (67)–(70). For every density operator $\rho$ on $(\mathbb C^d)^{\otimes n}$,
--
--   $$
--   F_{\mathrm{prod}}(\rho)\ge a\ \Longrightarrow\ \Pr[\text{accept}]\ge1-\frac\delta4,\qquad
--   F_{\mathrm{prod}}(\rho)\le b\ \Longrightarrow\ \Pr[\text{accept}]\le\frac\delta4 .
--   $$
--
--   This is the statistical part of Theorem 3.8: the ideal protocol already decides the promise problem.
--
--   Differences from the source:
--   - encoding: ρ ∈ D((ℂ^d)^{⊗n}), n ≥ 1, d ≥ 2 → ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ with WildeQIT.IsDensityOperator ρ (positive semidefinite, trace 1); reason: the computational basis of (ℂ^d)^{⊗n} is indexed by level strings Fin n → Fin d; same operators, sites and levels 0-based
--   - encoding: F_prod(ρ) as a maximum over unit vectors |π_i⟩ ∈ ℂ^d (2) → fprod ρ, the supremum of Re⟨π_1⊗⋯⊗π_n|ρ|π_1⊗⋯⊗π_n⟩ over families of unit vectors; reason: the set is nonempty and bounded and the supremum is attained (compactness); the form is real for Hermitian ρ, so the value is the printed maximum
--   - encoding: the parameters c, η, q, R, k, p_Y, p_N, T of (67)–(70) with ceilings → protoC, protoEta, protoQ, protoR, protoK, protoPY, protoPN, protoT with ⌈·⌉₊ (Nat.ceil) and the natural logarithm; reason: all ceiling arguments are positive under 1 ≥ a > b ≥ 0, δ ∈ (0,1/2); log is natural (p.8)
--   - reading: the statistical error is at most δ/4, and hence at most δ/2 → acceptance ≥ 1 − δ/4 on YES and ≤ δ/4 on NO; reason: the stronger of the two printed values
--   - encoding: Pr[accept] of Protocol 3.1 with exact measurements → idealAccept = Re Tr(P ρ^{⊗Tk}), P the threshold operator over T trials of {Q_k, I − Q_k}, trial j on copies jk, …, jk+k−1; reason: the Born rule for commuting projective measurements on disjoint copies
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), proof of Theorem 3.8, p.18

import Mathlib
import Definitions.Def_TolProdTest_fprod
import Definitions.Def_TolProdTest_idealAccept
import Definitions.Def_WildeQIT_IsDensityOperator

set_option autoImplicit false

open Matrix

namespace TolProdTest

/-- **Proof of Theorem 3.8, statistical step**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), p.18: "By Lemma 3.7, each trial has acceptance probability at
least p_Y in the YES case and at most p_N in the NO case. … At the threshold in Protocol 3.1, Hoeffding's
inequality bounds each error by exp(−T(p_Y − p_N)²/2). … Thus Equation (70) makes the statistical error on every
promised input at most δ/4, and hence at most δ/2."

The ideal Protocol 3.1 (exact local measurements, `T` trials of `k` copies, threshold `(p_Y + p_N)/2` on the mean)
accepts every density operator with `F_prod(ρ) ≥ a` with probability at least `1 − δ/4`, and every density operator
with `F_prod(ρ) ≤ b` with probability at most `δ/4`.

**Formalization Note** The protocol's acceptance probability is `idealAccept n d a b δ ρ`. Standing assumptions
(§3.4, p.17): `1 ≥ a > b ≥ 0`, `δ ∈ (0, 1/2)`, `n ≥ 1`, `d ≥ 2`. -/
theorem theorem_3_8_statistical (a b δ : ℝ) (hb : 0 ≤ b) (hab : b < a) (ha : a ≤ 1) (hδ : 0 < δ)
    (hδ2 : δ < 1 / 2) {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d)
    (ρ : Matrix (Config n d) (Config n d) ℂ) (hρ : WildeQIT.IsDensityOperator ρ) :
    (a ≤ fprod ρ → 1 - δ / 4 ≤ idealAccept n d a b δ ρ) ∧
      (fprod ρ ≤ b → idealAccept n d a b δ ρ ≤ δ / 4) := by sorry

end TolProdTest
