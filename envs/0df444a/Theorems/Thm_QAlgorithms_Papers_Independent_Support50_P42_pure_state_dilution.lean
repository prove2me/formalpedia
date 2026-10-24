-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P42_pure_state_dilution
-- name    : QAlgorithms.Papers.Independent.Support50.P42.pure_state_dilution
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:22:50.779647+00:00
-- url     : https://prove2.me/theorems/058ef9c9-5110-4a4f-a496-fcfa436687bb
-- title:
--   Entropy-efficient pure-state dilution
-- statement:
--   Let $|\psi\rangle_{AB}$ be any normalized pure state on positive finite local dimensions, and let $E=S(\rho_B)$ in bits. There are integer singlet budgets $m_n$ and local one-way preparation channels $\mathcal L_n$ such that
--
--   $$\lim_{n\to\infty}\frac{m_n}{n}=E,\qquad \lim_{n\to\infty}\frac12\left\|\mathcal L_n((\Psi^-)^{\otimes m_n})-(|\psi\rangle\langle\psi|)^{\otimes n}\right\|_1=0.$$
--
--   Each protocol requires at most $2m_n$ classical bits, corresponding to the direct compressed-teleportation method. If $E=0$, every $m_n$ may be zero. Vanishing trace distance is equivalent to fidelity tending to one for these pure targets. This states entropy-efficient dilution without imposing a mixed-state entropy formula or a later classical-communication improvement.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, PDF p. 4, §V: entropy-efficient pure-state dilution

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF pp.4,15--16: entropy-efficient pure-state dilution with global error
vanishing, and two cbits per compressed qubit in the direct method. No mixed
single-letter cost or later sublinear message refinement is claimed. -/
theorem pure_state_dilution (s : Shared) (hpure : IsPureShared s) :
    ∃ m : ℕ → ℕ, ∃ L : (n : ℕ) → Superop (Fin (2^(m n)) × Fin (2^(m n)))
      (Fin ((s.dims 0)^n) × Fin ((s.dims 1)^n)),
      (∀ n, FiniteLOCC (L n) ∧ OneWayBits (2*m n) (L n)) ∧
      Filter.Tendsto (fun n : ℕ => (m n : ℝ)/(n : ℝ)) Filter.atTop (nhds (ent s)) ∧
      Filter.Tendsto (fun n : ℕ => traceDistance (L n (singlets (m n)))
        (dimensionedPower (pairOfState s) n)) Filter.atTop (nhds (0 : ℝ)) ∧
      (ent s=0 → ∀ n, m n=0) := by sorry

end QAlgorithms.Papers.Independent.Support50.P42

end
