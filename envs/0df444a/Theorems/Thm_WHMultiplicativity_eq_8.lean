-- Prove2me | Theorems.Thm_WHMultiplicativity_eq_8
-- name    : WHMultiplicativity.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:23:12.633808+00:00
-- url     : https://prove2.me/theorems/68d5f669-3086-468d-b29d-95b18d57c056
-- title:
--   Eq. (8): $S(|\varphi\rangle\langle\varphi|) = \frac{1}{d-1}\big(\mathbb 1 - |\bar\varphi\rangle\langle\bar\varphi|\big)$
-- statement:
--   Let $d\ge2$, let $S$ be the Werner–Holevo channel on $d\times d$ matrices, and let $\varphi\in\mathbb C^d$ be a unit vector. Then
--
--   $$
--   S(|\varphi\rangle\langle\varphi|) = \frac{1}{d-1}\Big(\mathbb 1 - |\bar\varphi\rangle\langle\bar\varphi|\Big),
--   $$
--
--   where $\bar\varphi$ is the vector whose coordinates in the fixed basis are the complex conjugates of those of $\varphi$.
--
--   So every pure input is sent to $\frac1{d-1}$ times a rank-$(d-1)$ projection, and all pure inputs give outputs with the same spectrum.
--
--   Differences from the source:
--   - encoding: φ a pure input state; φ̄ its complex conjugate → φ : Fin d → ℂ with IsUnitVector φ; φ̄ = star φ (entrywise conjugate in the standard basis); reason: a pure state is a unit vector; conjugation in the fixed basis
--   - encoding: d × d matrices with denominator d − 1 (d ≥ 2 implicit) → hypothesis 2 ≤ d; reason: excludes only d = 1, where the page's formula divides by zero
-- source:
--   Werner and Holevo, Counterexample to an additivity conjecture for output purity of quantum channels, arXiv:quant-ph/0203003v1, eq. (8), p.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WHAdditivity_Renyi_Model

open WHAdditivity.Renyi

namespace WHMultiplicativity

/-- Werner and Holevo, arXiv:quant-ph/0203003v1, eq. (8), p.2: for a pure input,
`S(|φ⟩⟨φ|) = (1/(d − 1))(𝟙 − |φ̄⟩⟨φ̄|)`, where `φ̄` is the entrywise complex conjugate of `φ`
in the fixed basis.

**Formalization Note.** `φ` is a unit vector of `ℂ^d` (`IsUnitVector φ`, needed for
`tr |φ⟩⟨φ| = 1`), `|φ⟩⟨φ| = pureState φ`, and `φ̄ = star φ` (entrywise conjugate in the standard
basis). `2 ≤ d` is the paper's standing assumption. -/
theorem eq_8 (d : ℕ) (hd : 2 ≤ d) (φ : Fin d → ℂ) (hφ : IsUnitVector φ) :
    wernerHolevo d (pureState φ) = ((d : ℂ) - 1)⁻¹ • (1 - pureState (star φ)) := by sorry

end WHMultiplicativity
