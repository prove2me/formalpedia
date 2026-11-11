-- Prove2me | Theorems.Thm_SchattenSketch_Main_proposition_4_2
-- name    : SchattenSketch.Main.proposition_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:57:23.463363+00:00
-- url     : https://prove2.me/theorems/ea38ca89-5b4e-4ced-b598-a71e1eb4b4f7
-- title:
--   Proposition 4.2 — moment-matched scalar hard pair: equal moments through $K$, mean one, square-root gap $(1+\varepsilon)/2$
-- statement:
--   For every $0<\varepsilon<1$ there are an integer $M_\varepsilon\ge 6$ and a constant $\eta_\varepsilon>0$ such that, for every integer $K\ge 2$, there are $B_K$ and two probability laws $\nu_0,\nu_1$ on $[0,B_K]$, each supported on at most $K+2$ points, with
--   $$B_K\le 2(K+1)^{M_\varepsilon},\qquad \int x\,d\nu_0=\int x\,d\nu_1=1,\qquad \int x^q\,d\nu_0=\int x^q\,d\nu_1\ (0\le q\le K),$$
--   and, writing $h_b=\int\sqrt x\,d\nu_b$,
--   $$\eta_\varepsilon=\frac{1-\varepsilon}4,\qquad \frac{h_1-h_0}{h_1+h_0}\ge\frac{1+\varepsilon}2=\varepsilon+2\eta_\varepsilon,\qquad h_1\ge\frac1{2\sqrt2}.$$
--
--   The two laws are the scalar seeds of the lower bound: $x$ plays a squared singular value, so equal moments in $x$ hide the matrix moments while the square-root moments, which build the nuclear norm, stay separated.
--
--   **Formalization Note.** A law "on $[0,B_K]$ supported on at most $K+2$ points" is a probability measure on $\mathbb R$ carried by a finite set of at most $K+2$ points of $[0,B_K]$ (`IsSupportedOnAtMost`). All integrals are Bochner integrals of continuous functions against finitely supported probability measures, hence of integrable functions.
--
--   Differences from the source:
--   - encoding: probability laws ν_0, ν_1 on [0, B_K], each supported on at most K + 2 points → probability measures on ℝ with a finite set S ⊆ [0, B], |S| ≤ K + 2, ν(Sᶜ) = 0; reason: the same laws
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 14, Proposition 4.2, (4.P1)–(4.P3) (proof pp. 37–41, A.3)

import Mathlib
import Definitions.Def_SchattenSketch_Main_Path

open MeasureTheory

namespace SchattenSketch.Main

/-- Proposition 4.2 (moment-matched scalar hard pair; Yang, p. 14). For every `0 < ε < 1` there
are an integer `M_ε ≥ 6` and `η_ε = (1 - ε)/4 > 0` such that for every integer `K ≥ 2` there are
`B_K ≤ 2(K + 1)^{M_ε}` and two probability laws `ν₀, ν₁` on `[0, B_K]`, each carried by at most
`K + 2` points, with mean one, equal moments of order `0, …, K`, and square-root moments
`h_b = ∫ √x dν_b` satisfying `(h₁ - h₀)/(h₁ + h₀) ≥ (1 + ε)/2 = ε + 2η_ε` and `h₁ ≥ 1/(2√2)`. -/
theorem proposition_4_2 :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ M : ℕ, 6 ≤ M ∧ ∃ η : ℝ, 0 < η ∧ η = (1 - ε) / 4 ∧
        ∀ K : ℕ, 2 ≤ K →
          ∃ B : ℝ, B ≤ 2 * ((K : ℝ) + 1) ^ M ∧
          ∃ ν₀ ν₁ : Measure ℝ, IsProbabilityMeasure ν₀ ∧ IsProbabilityMeasure ν₁ ∧
            IsSupportedOnAtMost ν₀ (K + 2) B ∧ IsSupportedOnAtMost ν₁ (K + 2) B ∧
            ∫ x, x ∂ν₀ = 1 ∧ ∫ x, x ∂ν₁ = 1 ∧
            (∀ q : ℕ, q ≤ K → ∫ x, x ^ q ∂ν₀ = ∫ x, x ^ q ∂ν₁) ∧
            ((∫ x, Real.sqrt x ∂ν₁) - ∫ x, Real.sqrt x ∂ν₀) /
                ((∫ x, Real.sqrt x ∂ν₁) + ∫ x, Real.sqrt x ∂ν₀) ≥ (1 + ε) / 2 ∧
            (1 + ε) / 2 = ε + 2 * η ∧
            ∫ x, Real.sqrt x ∂ν₁ ≥ 1 / (2 * Real.sqrt 2) := by sorry

end SchattenSketch.Main
