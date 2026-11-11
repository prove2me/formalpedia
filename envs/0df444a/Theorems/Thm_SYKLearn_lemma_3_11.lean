-- Prove2me | Theorems.Thm_SYKLearn_lemma_3_11
-- name    : SYKLearn.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:45.095467+00:00
-- url     : https://prove2.me/theorems/2e3365d0-dc7e-42ad-bb28-0fda067e8377
-- title:
--   Lemma 3.11 — remaining thermal estimate: $c_{1,4}-2c^{\rm conn}_{3,8}\ge cb\,e^{-C\beta^2}$
-- statement:
--   Let $c_{1,4}$ and $c^{\rm conn}_{3,8}$ be the coefficients of Lemma 3.3 (the leading linear response and the connected degree-three response of the annealed Gibbs state). There are universal constants $c,C>0$ such that for every $\beta>0$, writing $b=\min\{\beta,1\}$, if $n\ge Cb^{-2}e^{C\beta^2}$ then
--
--   $$c_{1,4}-2c^{\rm conn}_{3,8}\ \ge\ c\,b\,e^{-C\beta^2}.$$
--
--   This is the margin that keeps the connected degree-three term from cancelling the leading signal in the commutator gap (Theorem 3.10).
--
--   **Formalization Note** The coefficients are the canonical ones of the definition module, which agree with the paper's whenever Lemma 3.3's identities determine them.
--
--   Differences from the source:
--   - generalization: the Majorana operators ψ_i of the paper's fixed representation on ℂ^{2^{n/2}} → every Hermitian CAR family Q.γ of a SYKFastMix.FastMixing.Model; reason: the statement is invariant under unitary conjugation, and every CAR family in dimension 2^{n/2} is unitarily equivalent to the paper's, so it specializes to the paper's operators
--   - encoding: g_I i.i.d. N(0, σ_n²), σ_n² = 6/n³ → disorderLaw Q (product of N(0, 6J²/N³)) with the hypothesis Q.J = 1; reason: with J = 1 the law is exactly the paper's; n even and n ≥ 4 come from Model
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Lemma 3.11, p.31 (proof App. B, pp.58–61)

import Mathlib
import Definitions.Def_SYKLearn_Coefficients

noncomputable section
open SYKFastMix.FastMixing

namespace SYKLearn

/-- **Lemma 3.11 (Remaining thermal estimate)**, p.31 (reprinted p.58) (Anshu–Arunachalam–Chen–
Hwang, *Efficiently Learning SYK Hamiltonians*, STOC 2027 submission, held file sha256
5d7d199a…). There are universal constants `c, C > 0` such that, for every `β > 0`, writing
`b = min{β, 1}`, if `n ≥ Cb^{−2}e^{Cβ²}`, then `c_{1,4} − 2c^conn_{3,8} ≥ cbe^{−Cβ²}`.

**Formalization Note.** `c_{1,4}` and `c^conn_{3,8}` are the canonical coefficients of Lemma 3.3
(`Definitions.Def_SYKLearn_Coefficients`). `Q.J = 1`; every CAR family. -/
theorem lemma_3_11 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ β : ℝ, 0 < β → ∀ (N : ℕ) (Q : Model N), Q.J = 1 →
      C * (min β 1)⁻¹ ^ 2 * Real.exp (C * β ^ 2) ≤ N →
        c * min β 1 * Real.exp (-(C * β ^ 2)) ≤ c14 β Q - 2 * cconn β Q := by sorry

end SYKLearn
