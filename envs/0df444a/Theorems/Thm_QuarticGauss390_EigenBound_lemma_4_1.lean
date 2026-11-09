-- Prove2me | Theorems.Thm_QuarticGauss390_EigenBound_lemma_4_1
-- name    : QuarticGauss390.EigenBound.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:31.153685+00:00
-- url     : https://prove2.me/theorems/74defd47-f56c-4899-89d0-8b8c80addd4e
-- title:
--   Lemma 4.1 — $H_{C^2}=6s^2I+[R^2]_4$ and $R^2\preceq\frac n4H_{C^2}-ns^2I$
-- statement:
--   Fix a CAR system on $n\ge2$ modes. For every homogeneous quartic $R=\sum_{|S|=4}r_Sc_S$ with real coefficients, let $C=C^R$ and $s=\sqrt{\tau[R^2]}$. Then
--   $$H_{C^2}=6s^2I+[R^2]_4,$$
--   where $[X]_4$ is the degree-four part of the Majorana expansion of $X$, and
--   $$R^2\preceq\frac n4H_{C^2}-ns^2I .$$
--
--   The square of a quartic operator is thus dominated by a quartic Hamiltonian whose coefficient matrix $C^2$ is positive semidefinite; Lemma 4.2 turns this into an operator-norm bound.
--
--   Differences from the source:
--   - encoding: $s=\sqrt{\tau[R^2]}$ → $\sqrt{\operatorname{Re}\tau[R^2]}$; $[X]_4$ → $\sum_{|S|=4}\tau[c_S^\dagger X]c_S$; $C^2$ → the matrix product $C^RC^R$; reason: $\tau[R^2]$ is real; the coefficients of the orthonormal monomial expansion (2.1)
-- source:
--   Ojas Parekh, Improved classical optimization of fermionic Hamiltonians beyond Gaussian states, STOC 2027 submission #390 (October 2026), source.pdf SHA-256 9018757e184cce1091160d8b5847294a0e6c16cc09386b1f2b6bb000f7542101, p.13, Lemma 4.1, eq. (4.1)–(4.2); [X]_k defined p.6

import Mathlib
import Definitions.Def_QuarticGauss390_EigenBound_CAR
import Definitions.Def_QuarticGauss390_EigenBound_Moments

open Matrix
open scoped ComplexOrder

namespace QuarticGauss390.EigenBound

/-- Lemma 4.1, p.13: for a homogeneous quartic `R`, `C = C^R`, `s = √τ[R²]`:
`H_{C²} = 6 s² I + [R²]_4` (4.1) and `R² ⪯ (n/4) H_{C²} - n s² I` (4.2). -/
theorem lemma_4_1 {n : ℕ} (hn : 2 ≤ n) (C : CAR n) (r : Finset (Fin (2 * n)) → ℝ) :
    let R := quartic C r
    let Cm := coefMatrix C R
    let s := sigma n R
    coefHam C (Cm * Cm) = ((6 * s ^ 2 : ℝ) : ℂ) • (1 : Op n) + degPart C 4 (R * R) ∧
    (((n : ℂ) / 4) • coefHam C (Cm * Cm) - ((n * s ^ 2 : ℝ) : ℂ) • (1 : Op n) - R * R).PosSemidef := by sorry

end QuarticGauss390.EigenBound
