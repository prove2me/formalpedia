-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_aeVartheta_overlap_le
-- name    : QAlgorithms.Nannicini.aeVartheta_overlap_le
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:46:19.08652+00:00
-- url     : https://prove2.me/theorems/96ee18e6-e3af-47ad-a6cd-400d6046035d
-- title:
--   Near-orthogonality of the two amplitude-estimation output states
-- statement:
--   Let $\theta \in (0, \pi/2)$ be the angle of the amplitude amplification setting, $S|0\rangle = \sin\theta\,|\psi_G\rangle + \cos\theta\,|\psi_B\rangle$, and let $m \ge 0$ be the number of qubits of the first register of the amplitude estimation circuit. Write $Q_m$ for the quantum Fourier transform on $m$ qubits (sign $+$, normalization $2^{-m/2}$) and define the first-register output states obtained when the second register holds the eigenstates $|\phi_\pm\rangle$ of the Grover operator:
--
--   $$
--   |\vartheta_\pm\rangle = Q_m^\dagger\Big(\frac{1}{\sqrt{2^m}}\sum_{k=0}^{2^m-1} e^{\pm 2i\theta k}|k\rangle\Big).
--   $$
--
--   Then
--
--   $$
--   |\langle \vartheta_-|\vartheta_+\rangle| \le \frac{1}{2^m \sin 2\theta}.
--   $$
--
--   Thus the two states become nearly orthogonal as $m$ grows; this is what makes a measurement of the second register return a marked item with probability close to $1/2$ in the search algorithm with an unknown number of marked items.
--
--   **Formalization Note** The source prints the conclusion as $O(1/(2^m\theta))$; with a constant uniform in $\theta$ that form is false near $\theta = \pi/2$, so the explicit bound that the source's proof derives is stated instead.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 92, Lemma 4.28. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
import Definitions.Def_QAlgorithms_Nannicini_Ch04c_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open scoped ENNReal

/-- Nannicini p.92–93, Lemma 4.28, in the explicit form its proof derives (p.93):
for `θ ∈ (0, π/2)` (standing assumption of §4.3.6, p.91) and any number `m` of qubits of the
first register, the phase-estimation output states `|ϑ±⟩ = Q_m† (2^{−m/2} Σ_k e^{±2iθk}|k⟩)`
satisfy `|⟨ϑ−|ϑ+⟩| ≤ 1/(2^m sin 2θ)`.

The printed conclusion `|⟨ϑ−|ϑ+⟩| = O(1/(2^m θ))` is false with a constant uniform in `θ`
(for `θ = π/2 − η` with `4η2^m ≪ 1` the overlap is close to `1`), and is only `O(1/2^m)` for
fixed `θ`; the explicit bound, which the proof states right before the `O`-form, is formalized
instead (trap 30; recorded in the chunk's `HARD.md`). -/
theorem aeVartheta_overlap_le (m : ℕ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ‖inner ℂ (aeVartheta m (-θ)) (aeVartheta m θ)‖ ≤ 1 / ((2 : ℝ) ^ m * Real.sin (2 * θ)) := by
  sorry











end QAlgorithms.Nannicini
