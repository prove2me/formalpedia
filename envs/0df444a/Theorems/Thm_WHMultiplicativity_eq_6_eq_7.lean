-- Prove2me | Theorems.Thm_WHMultiplicativity_eq_6_eq_7
-- name    : WHMultiplicativity.eq_6_eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:23:11.149643+00:00
-- url     : https://prove2.me/theorems/5b157734-cc2c-4bf3-86fe-d2c2506452b0
-- title:
--   Eqs. (6)–(7): $\frac{1}{d-1}(\operatorname{tr}(\rho)\mathbb 1-\rho^T) = \frac{1}{2(d-1)}\sum_{ij}(|i\rangle\langle j|-|j\rangle\langle i|)^*\rho(|i\rangle\langle j|-|j\rangle\langle i|)$
-- statement:
--   Let $d \ge 2$ and let $|1\rangle,\dots,|d\rangle$ be a fixed orthonormal basis of $\mathbb C^d$. For every complex $d\times d$ matrix $\rho$,
--
--   $$
--   \frac{1}{d-1}\Big(\operatorname{tr}(\rho)\,\mathbb 1 - \rho^T\Big) = \frac{1}{2(d-1)}\sum_{i,j}\big(|i\rangle\langle j| - |j\rangle\langle i|\big)^*\,\rho\,\big(|i\rangle\langle j| - |j\rangle\langle i|\big),
--   $$
--
--   where $\rho^T$ is the transpose in the fixed basis and $^*$ the adjoint.
--
--   The left side, form (6), shows that the Werner–Holevo map $S$ is linear and trace preserving; the right side, form (7), exhibits Kraus operators and so shows that $S$ is completely positive.
--
--   **Formalization Note** The left side is `WHAdditivity.Renyi.wernerHolevo d ρ`; $|i\rangle\langle j|$ is the matrix unit `Matrix.single i j 1` in the standard basis.
--
--   Differences from the source:
--   - encoding: S on the d × d matrices, argument written ρ → the identity for every X : Matrix (Fin d) (Fin d) ℂ; reason: the page defines S on all d × d matrices; same statement
--   - encoding: matrix transpose and conjugates with respect to some fixed basis → the standard basis of ℂ^d (index Fin d); reason: any fixed basis; the statement is the same up to a unitary change of basis
--   - encoding: d × d matrices with denominator d − 1 (d ≥ 2 implicit) → hypothesis 2 ≤ d; reason: excludes only d = 1, where the page's formula divides by zero
-- source:
--   Werner and Holevo, Counterexample to an additivity conjecture for output purity of quantum channels, arXiv:quant-ph/0203003v1, eqs. (6)–(7), p.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WHAdditivity_Renyi_Model

open scoped Matrix
open WHAdditivity.Renyi

namespace WHMultiplicativity

/-- Werner and Holevo, *Counterexample to an additivity conjecture for output purity of quantum
channels*, arXiv:quant-ph/0203003v1, eqs. (6)–(7), p.2: the two forms of the channel `S` on the
`d × d` matrices agree,
`S(ρ) = (tr(ρ)𝟙 − ρᵀ)/(d − 1) = (1/(2(d − 1))) Σ_{ij} (|i⟩⟨j| − |j⟩⟨i|)^* ρ (|i⟩⟨j| − |j⟩⟨i|)`
("The equality of the two forms is a straightforward exercise").

**Formalization Note.** `S` is `WHAdditivity.Renyi.wernerHolevo d`, form (6) extended linearly to
every matrix, and the identity is stated for every complex matrix `X`, not only density
matrices. `|i⟩⟨j|` is the matrix unit `Matrix.single i j 1` in the standard basis of `ℂ^d` (the
paper's fixed basis), and `^*` is the conjugate transpose. `2 ≤ d` is the paper's standing
assumption (the formula divides by `d − 1`). -/
theorem eq_6_eq_7 (d : ℕ) (hd : 2 ≤ d) (X : Matrix (Fin d) (Fin d) ℂ) :
    wernerHolevo d X =
      (2 * ((d : ℂ) - 1))⁻¹ • ∑ i : Fin d, ∑ j : Fin d,
        (Matrix.single i j (1 : ℂ) - Matrix.single j i 1)ᴴ * X *
          (Matrix.single i j (1 : ℂ) - Matrix.single j i 1) := by sorry

end WHMultiplicativity
