-- Prove2me | Theorems.Thm_SYKLearn_lemma_3_2
-- name    : SYKLearn.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:14.9862+00:00
-- url     : https://prove2.me/theorems/7ad59009-c3fc-4787-88d4-fe28ac4f12db
-- title:
--   Lemma 3.2 — commutator gap: $\ker M=\mathrm{span}\{g\}$ and $\|Mh\|_2\ge c\min\{\beta,1\}e^{-C\beta^2}\|h\|_2$ on $g^\perp$
-- statement:
--   Let $M=M_\beta$ be the direction matrix $(M_\beta)_{S,I}=-\mathrm{Tr}[\rho_{\beta,g}[\Gamma_S,\Gamma_I]]$, $|S|=6$, $|I|=4$. There are universal constants $c,C>0$ such that for every $\beta>0$ there are $C_\beta>0$ and $n_0(\beta)$ such that, for every even $n\ge n_0(\beta)$, with probability at least $1-C_\beta/n$ over $g$,
--
--   $$\ker M=\mathrm{span}\{g\}\qquad\text{and}\qquad \|Mh\|_2\ge\gamma_\beta\|h\|_2\ \text{ for every }h\perp g,\qquad \gamma_\beta=c\min\{\beta,1\}e^{-C\beta^2}.$$
--
--   The commutator equations $\mathrm{Tr}[\rho_{\beta,g}[\Gamma_S,H_h]]=0$ determine the coupling vector up to scale, and robustly: any approximate null vector is close to $\pm g/\|g\|_2$. This is the identifiability statement behind direction learning.
--
--   **Formalization Note** $M$ is a real matrix acting on $\mathbb R^{\binom{[n]}4}$; norms are Euclidean. The gap is stated in its explicit form, with $c,C$ chosen before $\beta$.
--
--   Differences from the source:
--   - generalization: the Majorana operators ψ_i of the paper's fixed representation on ℂ^{2^{n/2}} → every Hermitian CAR family Q.γ of a SYKFastMix.FastMixing.Model; reason: the statement is invariant under unitary conjugation, and every CAR family in dimension 2^{n/2} is unitarily equivalent to the paper's, so it specializes to the paper's operators
--   - encoding: g_I i.i.d. N(0, σ_n²), σ_n² = 6/n³ → disorderLaw Q (product of N(0, 6J²/N³)) with the hypothesis Q.J = 1; reason: with J = 1 the law is exactly the paper's; n even and n ≥ 4 come from Model
--   - encoding: with probability at least 1 − x over g → the complement of the good set has (outer) measure at most x; reason: equivalent for measurable events, and no measurability of the event is assumed
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Lemma 3.2, p.18 (proof p.32)

import Mathlib
import Definitions.Def_SYKLearn_Direction

noncomputable section
open Matrix MeasureTheory SYKFastMix.FastMixing

namespace SYKLearn

/-- **Lemma 3.2 (Commutator gap)**, p.18 (Anshu–Arunachalam–Chen–Hwang, *Efficiently Learning SYK
Hamiltonians*, STOC 2027 submission, held file sha256 5d7d199a…). For every fixed known `β > 0`,
there are constants `γ_β, C_β > 0` and `n₀(β)` such that, for every even `n ≥ n₀(β)`, the event
`ker M = span{g}`, `‖Mh‖₂ ≥ γ_β‖h‖₂` for every `h ⊥ g` holds with probability at least
`1 − C_β/n`. The gap can be chosen as `γ_β = c min{β, 1}e^{−Cβ²}` for universal constants
`c, C > 0`.

**Formalization Note.** `M = M_β` is `Mmat β Q g` ((28), p.18), a real matrix acting on
`ℝ^{C([n],4)}`; its kernel is that of `Matrix.toLin'`. `h ⊥ g` is `Σ_I h_I g_I = 0`; norms are
Euclidean. The gap is stated with its explicit form, `c, C` universal and chosen before `β`. Both
conjuncts are in the event; the bad set is bounded in outer measure. `Q.J = 1`; every CAR family. -/
theorem lemma_3_2 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ β : ℝ, 0 < β → ∃ Cβ : ℝ, ∃ n₀ : ℕ, 0 < Cβ ∧
      ∀ (N : ℕ) (Q : Model N), n₀ ≤ N → Q.J = 1 →
        disorderLaw Q {w | ¬ (LinearMap.ker (Matrix.toLin' (Mmat β Q w)) =
            Submodule.span ℝ {w} ∧
          ∀ h : Disorder N, ∑ I, h I * w I = 0 →
            c * min β 1 * Real.exp (-(C * β ^ 2)) * Real.sqrt (∑ I, h I ^ 2) ≤
              Real.sqrt (∑ S, (Mmat β Q w *ᵥ h) S ^ 2))} ≤
          ENNReal.ofReal (Cβ / N) := by sorry

end SYKLearn
