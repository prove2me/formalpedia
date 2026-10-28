-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P38_advantage_ceiling_and_equality
-- name    : QAlgorithms.Papers.Independent.Information100.P38.advantage_ceiling_and_equality
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:06:10.332785+00:00
-- url     : https://prove2.me/theorems/919af263-d1ef-4d9f-ba14-ffd0a576d7d5
-- title:
--   Proposition 1
-- statement:
--   Let $d,n\ge1$, let $H=\operatorname{diag}(E_0,\ldots,E_{d-1})$ have strictly increasing real energies, and let $M$ be an $n$-outcome POVM. Then
--
--   $$A_H^M\le \frac{\operatorname{Tr}H}{d}-E_0.$$
--
--   Equality holds exactly when there are a unit vector $\psi$ with $|\psi_i|^2=1/d$ for every $i$ and a subset $S$ of outcomes such that $\sum_{\mu\in S}M_\mu=|\psi\rangle\langle\psi|$ and $M_\mu\psi=0$ for every $\mu\notin S$. Every such witness state attains the maximum excess work. Zero effects may occur on either side of $S$. The characterization identifies all measurements that attain the universal ceiling.
-- source:
--   All coherent measurements provide observational ergotropic advantage, arXiv:2609.18735v1, PDF p. 5, Proposition 1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix

/-- Paper pp.5–6, Proposition 1: universal ceiling, complete equality characterization,
and attainment by every maximally coherent witness state. -/
theorem advantage_ceiling_and_equality {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (E : Fin d → ℝ) (hE : StrictMono E)
    (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (hM : IsPOVM M) :
    let ceiling := (∑ i, E i) / (d : ℝ) - E ⟨0, hd⟩
    observationalAdvantage E M ≤ ceiling ∧
    (observationalAdvantage E M = ceiling ↔ ∃ v S, advantageCeilingWitness M v S) ∧
    (∀ v S, advantageCeilingWitness M v S →
      observationalErgotropy E M (pureDensity v) - incoherentErgotropy E (pureDensity v) =
        observationalAdvantage E M) := by sorry

end QAlgorithms.Papers.Independent.Information100.P38

end
