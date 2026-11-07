-- Prove2me | Theorems.Thm_QuantumHMMR_theorem_1_3
-- name    : QuantumHMMR.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:41:08.21076+00:00
-- url     : https://prove2.me/theorems/90fc56e5-64f4-48ef-9d8a-0fe36edd441d
-- title:
--   Theorem 1.3 — refutation of the quantum HMMR conjecture
-- statement:
--   Let $G$ be a finite inverse-closed generating set of the two-qubit Clifford group modulo phase containing the identity, and let $\nu_n = (1 - m^{-1})\chi_n + m^{-1}\xi_n$ be the one-step law (8) of the walk on a ring of $n$ qubits: with probability $1 - 1/m$ a uniform gate of $G$ on a uniform ring edge, with probability $1/m$ a uniform rotation $e^{i\varphi Z}$ on the first qubit.
--
--   For each fixed integer $t \ge 4$ there are an integer $A_t \ge 1$ and a constant $\kappa_t > 0$ such that, for sufficiently large $n$, setting
--   $$
--   m = A_t n^2, \qquad T = 3m\lceil\log^2 n\rceil = O_t(n^2\log^2 n), \tag{9}
--   $$
--   the iterated ensemble $\nu_n^{*T}$ is an adaptive unitary $t$-design with negligible error,
--   $$
--   \delta_t(\nu_n^{*T}, \mu_H) \le e^{-\kappa_t\log^2 n}. \tag{10}
--   $$
--   Nevertheless, a uniform polynomial-time algorithm distinguishes this ensemble from Haar with constant advantage using $O(\log^2 n)$ parallel forward queries. The family $\{\nu_n\}$ is efficiently samplable and consists of one- and two-qubit gates.
--
--   Formally: for every logarithm base $\beta > 1$ there are a uniform polynomial-time family $(D_n)$ of copy tests and constants $C, c > 0$ such that for every admissible $G$ and every $t \ge 4$ there are $A \ge 1$, $\kappa > 0$, $C_t$ and $n_0$ with, for all $n \ge n_0$: $T \le C_t n^2\log^2 n$; $\delta_t(\nu_n^{*T}, \mu_H) \le e^{-\kappa\log^2 n}$; $D_n$ uses at most $C\log^2 n$ copies of $U|0^n\rangle$; its acceptance probability under $U \sim \nu_n^{*T}$ exceeds that under $U \sim \mu_H$ by at least $c$; and $\nu_n$ is efficiently samplable.
--
--   The theorem refutes the quantum analogue (Conjecture 1.2) of the Hoory–Magen–Myers–Rackoff conjecture: a local, efficiently samplable random circuit can match any constant number of Haar moments, even against adaptive queries, and still be efficiently distinguishable from Haar.
--
--   Differences from the source:
--   - reading: log² n, base not printed → (log_β n)² for an arbitrary base β > 1; reason: covers every reading of the base
--   - generalization: G is one fixed generating set (p.11); p.4 asserts that some family exists → every admissible generating set G; reason: the theorem holds for each G; existence follows since such a G exists (Finset.univ, proved in the verification file)
--   - generalization: a distinguisher with O(log² n) queries (p.12; O_t(log² n) on p.4) and constant advantage → one family D and constants C, c chosen before G, t and A; reason: the proof's h = 6⌈log² n⌉ and K = 12h + 10 depend only on n, and any c < 1/8 works
--   - generalization: distinguishes with constant advantage → signed advantage: walk acceptance minus Haar acceptance ≥ c; reason: implies the unsigned advantage
--   - reading: "constant advantage", "for sufficiently large n", "O_t(n² log² n)" → ∃ c > 0; ∃ n₀ depending on (β, G, t); ∃ C_t with T ≤ C_t n² log² n; reason: the meaning of the asymptotic notation
--   - reading: an efficiently samplable family on one- and two-qubit gates (p.4) → IsEfficientlySamplable G n m: a uniform discrete seed of O(log m + log n) bits plus an ideal uniform real angle, a polynomial-time instruction map, and outputs acting on at most two neighbouring qubits; reason: footnote 4 (p.11) handles the angle discretization and omits its details
--   - encoding: a uniform polynomial-time algorithm with parallel forward queries → IsUniformFamily of CopyTest circuits on K copies of U|0ⁿ⟩ over the gates H, T, CNOT, CRot, measurements deferred; reason: the QPT model of p.11 fixes no gate set; the test of Lemma 4.4 needs exact uniform choices (CRot)
--   - encoding: δ_t(ν, μ_H) ∈ [0, 1] → the ℝ≥0∞-valued advantage; reason: same value; no junk supremum
--   - encoding: C_n finite → Fintype (Clifford.ProjectiveGroup n) supplied as an instance argument for every n; reason: a true fact; uniform laws do not depend on the enumeration
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Theorem 1.3, Eqs. (9), (10), p.12 (first statement p.4)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
import Definitions.Def_QuantumHMMR_IsCliffordGenSet
import Definitions.Def_QuantumHMMR_walkLaw
import Definitions.Def_QuantumHMMR_advantage
import Definitions.Def_QuantumHMMR_CopyTest
import Definitions.Def_QuantumHMMR_IsUniformFamily
import Definitions.Def_QuantumHMMR_IsEfficientlySamplable
import Definitions.Def_QuantumHMMR_logSq

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory

namespace QuantumHMMR

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

/-- **Theorem 1.3** (refutation of quantum HMMR; Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), p.12, first stated on p.4).
Let `G` be a finite inverse-closed generating set of the two-qubit Clifford group modulo phase,
containing the identity, and let `ν_n = (1 - m⁻¹) χ_n + m⁻¹ ξ_n` be the local walk of Eq. (8) on a
ring of `n` qubits. For each fixed integer `t ≥ 4` there are an integer `A_t ≥ 1` and a constant
`κ_t > 0` such that, for sufficiently large `n`, setting `m = A_t n²` and
`T = 3m⌈log² n⌉ = O_t(n² log² n)` (9), the iterated ensemble `ν_n^{*T}` is an adaptive unitary
`t`-design with negligible error `δ_t(ν_n^{*T}, μ_H) ≤ e^{-κ_t log² n}` (10). Nevertheless, a uniform
polynomial-time algorithm distinguishes this ensemble from Haar with constant advantage using
`O(log² n)` parallel forward queries. The family `{ν_n}` is efficiently samplable by one- and
two-qubit gates (p.4).

The Lean statement: for every log base `β > 1` there are a uniform polynomial-time family `D` of
copy tests and constants `C, c > 0` such that for every generating set `G` and every `t ≥ 4` there
are `A ≥ 1`, `κ > 0`, `C_t` and `n₀` with, for all `n ≥ n₀` (`m = A n²`, `T = 3m⌈log² n⌉`):
`T ≤ C_t n² log² n`; `δ_t(ν_n^{*T}, μ_H) ≤ e^{-κ log² n}`; `D n` uses at most `C log² n` copies; the
acceptance of `D n` on copies of `U|0ⁿ⟩` is at least `c` larger under `U ∼ ν_n^{*T}` than under
`U ∼ μ_H`; and `ν_n` is efficiently samplable.

**Formalization Note** `δ_t` is the `ℝ≥0∞`-valued `advantage` over all adaptive `t`-query
algorithms (any number of ancillas) and all effects; `μ_H` is the published `haarLaw`. The
distinguisher is one family for all `G, t, A`, given `1ⁿ`; it is not limited to `t` queries. The
finiteness of the Clifford group modulo phase is an instance argument. -/
theorem theorem_1_3 [∀ n, Fintype (Clifford.ProjectiveGroup n)] :
    ∀ β : ℝ, 1 < β →
      ∃ D : (n : ℕ) → CopyTest n, IsUniformFamily (fun n : ℕ => List.replicate n true) (fun n => n) D ∧
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ G : Finset (Clifford.ProjectiveGroup 2), IsCliffordGenSet G →
      ∀ t : ℕ, 4 ≤ t →
        ∃ A : ℕ, 1 ≤ A ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ Ct : ℝ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
          let m := A * n ^ 2
          let T := 3 * m * ⌈logSq β n⌉₊
          (T : ℝ) ≤ Ct * (n : ℝ) ^ 2 * logSq β n ∧
          advantage t (walkLaw G n m T) (haarLaw n) ≤ ENNReal.ofReal (Real.exp (-(κ * logSq β n))) ∧
          ((D n).K : ℝ) ≤ C * logSq β n ∧
          c ≤ (∫ U, (D n).accept (act U (zeroKet n)) ∂walkLaw G n m T) -
            ∫ U, (D n).accept (act U (zeroKet n)) ∂haarLaw n ∧
          IsEfficientlySamplable G n m := by sorry

end QuantumHMMR
