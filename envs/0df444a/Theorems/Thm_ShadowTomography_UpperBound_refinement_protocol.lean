-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_refinement_protocol
-- name    : ShadowTomography.UpperBound.refinement_protocol
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-07T07:25:23.928065+00:00
-- url     : https://prove2.me/theorems/7737ec64-dd9b-4d74-930e-4170ac6316ef
-- title:
--   Aaronson's refinement protocol with explicit parameters
-- statement:
--   There is a universal constant $C_0>0$ such that the following holds. Let $D,M\ge2$, $0<\varepsilon\le\frac12$, $0<\delta\le\frac12$, and let $q,\ell,v,T$ be natural numbers with
--   $$
--   q\ge \frac{C_0(1+\log T)}{\varepsilon^2},\qquad
--   T\ge \frac{C_0\,q\log D}{\varepsilon},\qquad
--   \ell\ge C_0\log^4 M\,\big(1+\log\log M+\log(T/\delta)\big),\qquad
--   v\ge \frac{C_0(1+\log(T/\delta))}{\varepsilon^2}.
--   $$
--   Then for every family $E_1,\dots,E_M$ of two-outcome measurements on $\mathbb C^D$ there is a measurement $P$ of $T(q\ell+v)$ copies, with finite outcome set $\Omega$, together with estimates $b:\Omega\to[0,1]^M$, such that for every state $\rho$,
--   $$
--   \Pr_{\omega\sim P(\rho^{\otimes T(q\ell+v)})}\Big[\ |b_i(\omega)-\operatorname{Tr}(E_i\rho)|\le\varepsilon\ \text{ for all } i\ \Big]\ge1-\delta .
--   $$
--
--   This is the correctness statement of the iterative procedure in Aaronson's proof of Theorem 2 (§5): $T$ rounds, each spending $q\ell$ fresh copies on Gentle Search over the $2M$ amplified tests ($\ell$ registers of $q$ copies each) and $v$ fresh copies on checking the test it finds, followed by post-selection of the classical hypothesis. The parameters are explicit and tuned so that Chernoff bounds compose with the quantum union bound for every $T$. Theorem 2's copy bound follows by choosing $q,T,\ell,v$ as small as allowed.
--
--   **Formalization Note** The measurement uses exactly $T(q\ell+v)$ copies (unused copies are ignored); the paper's "if no index is found, halt" step is realised by the explicit verification on $v$ copies.
-- source:
--   S. Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, https://arxiv.org/abs/1711.01053, Section 5 (proof of Theorem 2), pp. 15-19

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_ShadowTomography_UpperBound_POVM
import Definitions.Def_ShadowTomography_UpperBound_ampMeasurements
import Definitions.Def_ShadowTomography_UpperBound_avgMarginal
import Definitions.Def_ShadowTomography_UpperBound_seqAccept
set_option autoImplicit false

open scoped ComplexOrder MatrixOrder

namespace ShadowTomography.UpperBound

/-- **K0 (refinement protocol).** Aaronson's §5 procedure with explicit parameters: `T` rounds,
each spending `q ℓ` fresh copies on Gentle Search over the `2M` amplified tests (`q` copies per
amplified register, `ℓ` registers) and `v` fresh copies on verifying the found index, then
post-selecting the classical hypothesis. When `q, T, ℓ, v` exceed the stated thresholds, the
procedure measures `T (q ℓ + v)` copies (unused copies are ignored) and estimates every `Tr(E_i ρ)` to within `ε` with
probability at least `1 - δ`, for every state `ρ`. -/
theorem refinement_protocol :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (D M : ℕ) (ε δ : ℝ) (q ℓ v T : ℕ), 2 ≤ D → 2 ≤ M → 0 < ε → ε ≤ 1 / 2 → 0 < δ →
        δ ≤ 1 / 2 →
        C₀ * (1 + Real.log T) / ε ^ 2 ≤ (q : ℝ) →
        C₀ * q * Real.log D / ε ≤ (T : ℝ) →
        C₀ * Real.log M ^ 4 * (1 + Real.log (Real.log M) + Real.log (T / δ)) ≤ (ℓ : ℝ) →
        C₀ * (1 + Real.log (T / δ)) / ε ^ 2 ≤ (v : ℝ) →
        ∀ E : Fin M → Matrix (Fin D) (Fin D) ℂ, (∀ i, IsEffect (E i)) →
          ∃ (Ω : Type) (_ : Fintype Ω) (P : POVM Ω (Fin (T * (q * ℓ + v)) → Fin D))
            (b : Ω → Fin M → ℝ),
            (∀ ω i, b ω i ∈ Set.Icc (0 : ℝ) 1) ∧
            ∀ ρ : Matrix (Fin D) (Fin D) ℂ, WildeQIT.IsDensityOperator ρ →
              1 - δ ≤ P.prob (tensorPow ρ (T * (q * ℓ + v)))
                (fun ω => ∀ i, |b ω i - ((E i) * ρ).trace.re| ≤ ε) := by
  sorry

end ShadowTomography.UpperBound
