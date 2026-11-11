-- Prove2me | Theorems.Thm_SYKLearn_theorem_3_10
-- name    : SYKLearn.theorem_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:16:52.132773+00:00
-- url     : https://prove2.me/theorems/14c37f84-16b7-441b-80e7-4a39dca3d641
-- title:
--   Theorem 3.10 — correlation with signal: $-\langle[\bar\rho_{4,8},H_h]|_{\mathbb M_6},[H_g,H_h]|_{\mathbb M_6}\rangle\ge c_\beta\|h\|_2^2$ for all $h\perp g$
-- statement:
--   Let $\bar\rho_{4,8}=\bar\rho_4+\bar\rho_8$ be the degree-$4$ and degree-$8$ parts of the annealed Gibbs state, and for $h\in\mathbb M_4$ let $H_h=\sum_Ih_I\Gamma_I$. There are universal constants $c,C>0$ such that for every $\beta>0$ there are $C_\beta,n_0(\beta)>0$ such that, for every even $n\ge n_0(\beta)$, with probability at least $1-C_\beta/n$ over the couplings $g$,
--
--   $$-\Big\langle[\bar\rho_{4,8},H_h]\big|_{\mathbb M_6},\ [H_g,H_h]\big|_{\mathbb M_6}\Big\rangle\ \ge\ c_\beta\|h\|_2^2\qquad\text{for every }h\perp g,\qquad c_\beta=c\min\{\beta,1\}e^{-C\beta^2}.$$
--
--   Here $h\perp g$ means $\sum_Ih_Ig_I=0$ and $\langle\cdot,\cdot\rangle$ is the inner product of coefficient vectors on $6$-sets.
--
--   The thermal commutator is positively correlated with the reference commutator $[H_g,H_h]$ uniformly over directions orthogonal to $g$; with Cauchy–Schwarz this gives the gap of Lemma 3.2.
--
--   **Formalization Note** The inner product is written as the real part of $\sum_S\overline{x_S}y_S$; both vectors are real. $c,C$ are chosen before $\beta$; $C_\beta,n_0$ after.
--
--   Differences from the source:
--   - generalization: the Majorana operators ψ_i of the paper's fixed representation on ℂ^{2^{n/2}} → every Hermitian CAR family Q.γ of a SYKFastMix.FastMixing.Model; reason: the statement is invariant under unitary conjugation, and every CAR family in dimension 2^{n/2} is unitarily equivalent to the paper's, so it specializes to the paper's operators
--   - encoding: g_I i.i.d. N(0, σ_n²), σ_n² = 6/n³ → disorderLaw Q (product of N(0, 6J²/N³)) with the hypothesis Q.J = 1; reason: with J = 1 the law is exactly the paper's; n even and n ≥ 4 come from Model
--   - encoding: with probability at least 1 − x over g → the complement of the good set has (outer) measure at most x; reason: equivalent for measurable events, and no measurability of the event is assumed
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Theorem 3.10, p.31 (proof pp.31–32)

import Mathlib
import Definitions.Def_SYKLearn_Direction

noncomputable section
open MeasureTheory SYKFastMix.FastMixing

namespace SYKLearn

/-- **Theorem 3.10 (Correlation with signal)**, p.31 (Anshu–Arunachalam–Chen–Hwang, *Efficiently
Learning SYK Hamiltonians*, STOC 2027 submission, held file sha256 5d7d199a…). For every fixed
`β > 0`, there are constants `C_β, n₀(β) > 0` such that, for every even `n ≥ n₀(β)`, with
probability at least `1 − C_β/n`,
`−⟨[ρ̄_{4,8}, H_h]|M_6, [H_g, H_h]|M_6⟩ ≥ c_β‖h‖₂²` for every `h ⊥ g`, where
`c_β = c min{β, 1}e^{−Cβ²}` for universal constants `c, C > 0`.

**Formalization Note.** `ρ̄_{4,8} = ρ̄_4 + ρ̄_8` is the annealed component of p.19 (`rho48`), as
the operator `H_{ρ̄_{4,8}} = ham Q (rho48 β Q w)`. `X|M_6` is the coefficient vector on `6`-sets
and `⟨·,·⟩` its inner product, written as the real part of `Σ_S \overline{x_S} y_S` (both vectors
are real). `h ⊥ g` is `Σ_I h_I g_I = 0` and `‖h‖₂² = Σ_I h_I²`. `c, C` are chosen before `β`,
`C_β, n₀` after. The bad set is bounded in outer measure. `Q.J = 1`; every CAR family. -/
theorem theorem_3_10 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ β : ℝ, 0 < β → ∃ Cβ : ℝ, ∃ n₀ : ℕ, 0 < Cβ ∧ 0 < n₀ ∧
      ∀ (N : ℕ) (Q : Model N), n₀ ≤ N → Q.J = 1 →
        disorderLaw Q {w | ¬ ∀ h : Disorder N, ∑ I, h I * w I = 0 →
          c * min β 1 * Real.exp (-(C * β ^ 2)) * ∑ I, h I ^ 2 ≤
            -(∑ S : SYKEdge.KSet N 6,
              star (coeff Q (ham Q (rho48 β Q w) * hamiltonian Q h -
                hamiltonian Q h * ham Q (rho48 β Q w)) S.1) *
              coeff Q (hamiltonian Q w * hamiltonian Q h -
                hamiltonian Q h * hamiltonian Q w) S.1).re} ≤
          ENNReal.ofReal (Cβ / N) := by sorry

end SYKLearn
