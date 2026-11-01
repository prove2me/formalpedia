-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P11_randomness_canBeFixed
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P11.randomness_canBeFixed
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:48:56.366128+00:00
-- url     : https://prove2.me/theorems/68c4f67d-c962-4b98-95ad-def3365d2d7b
-- title:
--   Shared and private random data can be fixed
-- statement:
--   Fix a finite normalized pure ensemble $\mathcal E=\{p_i,|v_i\rangle_{AB}\}$ in finite-dimensional complex Hilbert spaces, a positive blocklength $n$, and positive compressed dimensions $d_A,d_B$. Let $(\Omega,\mu)$ be a probability space for all input-independent random data, including the decoder's random data. For each seed $s\in\Omega$, let $c_s$ consist of independent local CPTP encoders with these same output dimensions and a joint CPTP decoder. Define its ensemble-average squared fidelity by
--
--   $$
--   F(c_s)=\sum_{i^n}\Bigl(\prod_{t=1}^np_{i_t}\Bigr)
--   \langle v_{i^n}|c_s(|v_{i^n}\rangle\langle v_{i^n}|)|v_{i^n}\rangle,
--   \qquad |v_{i^n}\rangle=\bigotimes_{t=1}^n|v_{i_t}\rangle.
--   $$
--
--   If $s\mapsto F(c_s)$ is measurable, it is integrable and there is a seed $s_0$ such that
--
--   $$
--   F(c_{s_0})\ge\int_\Omega F(c_s)\,d\mu(s).
--   $$
--
--   Thus fixing all random data preserves the dimension budgets without reducing the randomized average fidelity. Applied at each blocklength, this removes shared or private randomness from the achievable-rate criterion.
-- source:
--   On the distributed compression of quantum information, arXiv:quant-ph/0403042v3, PDF p. 3, Section II: shared and private randomness can be fixed

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P11

open MeasureTheory Filter

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Dependency50.P19 (both)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, Section II: fixing every party's random data yields a valid deterministic
code with the same dimension budgets and fidelity at least its randomized average.
Measurability plus the normalized-source/channel bounds ensures genuine integrability. -/
theorem randomness_canBeFixed {I A B Omega : Type*}
    [Fintype I] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (htotal : ∑ i, p i = 1)
    (v : I → EuclideanSpace ℂ (A × B)) (hv : ∀ i, IsState (v i))
    (n da db : ℕ) (codes : Omega → DistributedBlockCode A B n da db)
    (hmeas : Measurable (fun seed => finiteFidelity p v (codes seed))) :
    Integrable (fun seed => finiteFidelity p v (codes seed)) mu ∧
      ∃ seed, (∫ s, finiteFidelity p v (codes s) ∂mu) ≤ finiteFidelity p v (codes seed) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P11

end
