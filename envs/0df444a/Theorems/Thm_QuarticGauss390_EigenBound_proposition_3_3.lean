-- Prove2me | Theorems.Thm_QuarticGauss390_EigenBound_proposition_3_3
-- name    : QuarticGauss390.EigenBound.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:37.146028+00:00
-- url     : https://prove2.me/theorems/c792e68a-cc59-4d26-8c1c-c277aabec036
-- title:
--   Proposition 3.3 — a mixture $\omega$ of at most $\binom d4+1$ Gaussians with $M^\omega-2I\preceq M^\rho\preceq M^\omega+2I$
-- statement:
--   Fix a CAR system on $n\ge2$ modes, $d=2n$. For every density matrix $\rho$ there is a mixture
--   $$\omega=\sum_{k=1}^{K}p_k\,|g_k\rangle\langle g_k|,\qquad p_k\ge0,\ \sum_kp_k=1,\ |g_k\rangle\ \text{Gaussian},\ K\le\binom d4+1,$$
--   such that
--   $$M^\omega-2I_m\preceq M^\rho\preceq M^\omega+2I_m,$$
--   and equivalently $\|M^\rho-M^\omega\|_{\mathrm{op}}\le2$.
--
--   Every quartic moment matrix of a physical state is within operator-norm distance $2$ of the moment matrix of a Gaussian mixture of bounded size; this is the paper's central approximation result.
--
--   Differences from the source:
--   - encoding: "a mixture of at most $\binom d4+1$ pure Gaussian states" → a family indexed by `Fin K`, $K\le\binom{2n}4+1$, with nonnegative weights summing to 1; both Loewner inequalities and the operator-norm form are stated; reason: same object (repeated states are allowed and merge)
-- source:
--   Ojas Parekh, Improved classical optimization of fermionic Hamiltonians beyond Gaussian states, STOC 2027 submission #390 (October 2026), source.pdf SHA-256 9018757e184cce1091160d8b5847294a0e6c16cc09386b1f2b6bb000f7542101, p.12, Proposition 3.3, eq. (3.10)

import Mathlib
import Definitions.Def_QuarticGauss390_EigenBound_CAR
import Definitions.Def_QuarticGauss390_EigenBound_Gaussian
import Definitions.Def_QuarticGauss390_EigenBound_Moments
import Definitions.Def_QuarticGauss390_EigenBound_MatrixNorms

open Matrix

namespace QuarticGauss390.EigenBound

/-- Proposition 3.3, p.12: for every density matrix `ρ` there is a mixture
`ω = ∑_k p_k |g_k⟩⟨g_k|` of at most `C(d,4) + 1` pure Gaussian states with
`M^ω - 2 I_m ⪯ M^ρ ⪯ M^ω + 2 I_m` (3.10), equivalently `‖M^ρ - M^ω‖_op ≤ 2`. -/
theorem proposition_3_3 {n : ℕ} (hn : 2 ≤ n) (C : CAR n) (ρ : Op n) (hρ : IsDensity ρ) :
    ∃ (K : ℕ) (p : Fin K → ℝ) (g : Fin K → Vec n),
      K ≤ (2 * n).choose 4 + 1 ∧ (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1 ∧
      (∀ k, IsGaussian C (g k)) ∧
      let ω : Op n := ∑ k, (p k : ℂ) • pureProj (g k)
      (momentMatrix C ρ -
          (momentMatrix C ω - (2 : ℝ) • (1 : Matrix (Pair n) (Pair n) ℝ))).PosSemidef ∧
      (momentMatrix C ω + (2 : ℝ) • (1 : Matrix (Pair n) (Pair n) ℝ) -
          momentMatrix C ρ).PosSemidef ∧
      opNorm (momentMatrix C ρ - momentMatrix C ω) ≤ 2 := by sorry

end QuarticGauss390.EigenBound
