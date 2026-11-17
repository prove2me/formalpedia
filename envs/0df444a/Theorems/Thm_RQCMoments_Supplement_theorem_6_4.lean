-- Prove2me | Theorems.Thm_RQCMoments_Supplement_theorem_6_4
-- name    : RQCMoments.Supplement.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:52:37.8943+00:00
-- url     : https://prove2.me/theorems/e7d4aae5-61e3-4ec5-8681-81ccf9e8813c
-- title:
--   Theorem 6.4 — operator-norm approximation of a Haar unitary gives Kolmogorov closeness of $|\langle\varphi|U|\psi\rangle|^2$
-- statement:
--   Let $d\ge2$, let $V\sim\mathrm{Haar}(d)$, and let $C$ be a $d\times d$ random matrix, possibly dependent on $V$, such that
--
--   $$\Pr\big[\|C-V\|_{\mathrm{op}}\le\varepsilon\big]\ge1-\delta .$$
--
--   For fixed unit vectors $\psi,\varphi\in\mathbb C^d$ let $f(U)=|\langle\varphi|U|\psi\rangle|^2$. Then
--
--   $$\sup_{t\in\mathbb R}\big|F_{f(C)}(t)-F_{f(V)}(t)\big|\le\delta+2\sqrt{d-1}\,\varepsilon ,$$
--
--   where $F_X$ is the distribution function of $X$.
--
--   It lets a Haar random local unitary be replaced by an efficiently implementable circuit that approximates it in operator norm, at a controlled cost in Kolmogorov distance.
--
--   **Formalization Note** $V$ and $C$ live on one probability space; $V$ has law Haar and $C$ is measurable entrywise (it need not be unitary). $\|\cdot\|_{\mathrm{op}}$ is the operator norm for the Euclidean norm on $\mathbb C^d$. Unit vectors are coordinate vectors with $\sum_i|\varphi_i|^2=1$. The tolerance $\varepsilon$ is taken nonnegative.
--
--   Differences from the source:
--
--   - reading: tolerance ε in Pr[‖C − V‖op ≤ ε] ≥ 1 − δ (sign not stated) → 0 ≤ ε; reason: a norm tolerance is nonnegative; for ε < 0 the event is empty and the printed bound fails (d = 2, ε = −1, δ = 1: the hypothesis holds and the bound is 1 − 2 < 0)
--   - encoding: d × d random matrix C → C : Ω → ℂ^{d×d} with every entry measurable; reason: entrywise measurability is measurability for the Borel σ-algebra of ℂ^{d×d}
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 6.4, (148)–(149), p.40 (PDF p.42)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

namespace Supplement

/-- **Theorem 6.4** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 6.4, (148)–(149), p.40, PDF p.42).
For `d ≥ 2`, let `V ∼ Haar(d)` and let `C` be a `d × d` random matrix (possibly dependent on `V`)
such that `Pr[‖C − V‖_op ≤ ε] ≥ 1 − δ` (148). Then for `f(U) := |⟨φ|U|ψ⟩|²` with any fixed unit
vectors `ψ, φ`, `sup_{t∈ℝ} |F_{f(C)}(t) − F_{f(V)}(t)| ≤ δ + 2√(d−1) ε` (149), where `F_X` is the
distribution function of `X`.

**Formalization Note** `V` and `C` live on one probability space `(Ω, P)`; `V : Ω → U(d)` has law
`Haar(d)` (published `QAlgorithms.Schur.unitaryHaar`) and `C : Ω → ℂ^{d×d}` is measurable entrywise (a
random matrix; it need not be unitary). `‖·‖_op` is the operator norm on `ℂ^d` with the Euclidean norm
(`Matrix.toEuclideanCLM`). `⟨φ|M|ψ⟩ = ∑ᵢ conj(φᵢ) (Mψ)ᵢ`; unit vectors have `∑ᵢ |φᵢ|² = 1`. The
supremum over `t` is a bound for every real `t`. `ε ≥ 0` is added: `ε` is a tolerance in a norm
bound, and for `ε < 0` the event in (148) is empty and the statement fails (take `δ = 1`). -/
theorem theorem_6_4 (d : ℕ) (hd : 2 ≤ d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (V : Ω → Matrix.unitaryGroup (Fin d) ℂ)
    (hV : P.map V = QAlgorithms.Schur.unitaryHaar d)
    (C : Ω → Matrix (Fin d) (Fin d) ℂ) (hC : ∀ i j, Measurable (fun ω => C ω i j)) (ε δ : ℝ) (hε : 0 ≤ ε)
    (hclose : 1 - δ ≤ (P {ω | ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
      (C ω - (V ω : Matrix (Fin d) (Fin d) ℂ))‖ ≤ ε}).toReal)
    (φ ψ : Fin d → ℂ) (hφ : ∑ i, Complex.normSq (φ i) = 1) (hψ : ∑ i, Complex.normSq (ψ i) = 1) :
    let f : Matrix (Fin d) (Fin d) ℂ → ℝ := fun M => Complex.normSq (∑ i, star (φ i) * (M.mulVec ψ) i)
    ∀ t : ℝ, |(P {ω | f (C ω) ≤ t}).toReal - (P {ω | f (V ω : Matrix (Fin d) (Fin d) ℂ) ≤ t}).toReal| ≤
      δ + 2 * Real.sqrt ((d : ℝ) - 1) * ε := by sorry

end Supplement

end RQCMoments
