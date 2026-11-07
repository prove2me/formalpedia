-- Prove2me | Theorems.Thm_RobustQSC_proposition_4
-- name    : RobustQSC.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:50:59.564994+00:00
-- url     : https://prove2.me/theorems/5558ed20-fc7a-4d50-8e88-eeff53beb773
-- title:
--   Proposition 4, p.21 — $\mathrm{Tr}[A_f|g\rangle\langle g|]\le1-c+o(1)$ on $f^\perp$
-- statement:
--   With all but $2^{-\Omega(n)}$ probability over a Haar-random target state $|f\rangle$, for all pure states $|g\rangle$ orthogonal to $|f\rangle$,
--
--   $$
--   \mathrm{Tr}[A_f|g\rangle\langle g|]\le1-c+o(1),
--   $$
--
--   for some constant $c>0$, where $A_f$ is the acceptance operator of $|f\rangle$. Theorem 1's soundness follows by writing $A_f\preceq|f\rangle\langle f|+(1-c+o(1))(I-|f\rangle\langle f|)$.
--
--   Differences from the source:
--   - encoding: "with probability $1-2^{-\Omega(n)}$", "for $n$ large" → a constant $c_0>0$ and a threshold $n_0$ with the outer measure of the failure event at most $2^{-c_0n}$ for $n\ge n_0$; reason: the standard meaning; the failure event is bounded in outer measure, so no measurability is assumed
--   - encoding: $o(1)$ and "some constant $c$" → one sequence $e_n\to0$ and one $c>0$, chosen before $n$; reason: the standard meaning; the theorem has one $c$ and one $o(1)$
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), Proposition 4, p.21

import Definitions.Def_RobustQSC_accOp
import Definitions.Def_QAlgorithms_Defs_HaarTargetStates

namespace RobustQSC

open QAlgorithms QAlgorithms.TwoBasisCertification MeasureTheory Filter Topology

/-- **Proposition 4.** With all but `2^{−Ω(n)}` probability over a Haar-random target state
`|f⟩`, for all pure states `|g⟩` orthogonal to `|f⟩`, `Tr[A_f|g⟩⟨g|] ≤ 1 − c + o(1)` for some
constant `c > 0`, where `A_f` is the acceptance operator of the target state `|f⟩`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles for
total influence*, arXiv:2607.27184 (sha256 09d2692e…), Proposition 4, p.21.

**Formalization Note.** `c`, the `o(1)` sequence `e → 0` and the `Ω(n)` constant `c₀` are chosen
before `n`, for `n ≥ n₀`; the `∀ g` is inside the event. `Tr[A_f|g⟩⟨g|]` is
`effectProb (accOp f) (pureDensity g)`. -/
theorem proposition_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ n₀ : ℕ,
      ∀ n, n₀ ≤ n →
        haarTargetLaw n {f | IsState f ∧ ∃ g : EuclideanSpace ℂ (Qubits n), IsState g ∧
            inner ℂ f g = 0 ∧ 1 - c + e n < effectProb (accOp f) (pureDensity g)}
          ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(c₀ * n))) := by sorry

end RobustQSC
