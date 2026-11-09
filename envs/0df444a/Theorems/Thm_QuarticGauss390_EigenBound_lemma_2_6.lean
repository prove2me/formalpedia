-- Prove2me | Theorems.Thm_QuarticGauss390_EigenBound_lemma_2_6
-- name    : QuarticGauss390.EigenBound.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:17.787207+00:00
-- url     : https://prove2.me/theorems/7a64b3b2-eb70-476d-ae48-2aa582ce5c82
-- title:
--   Lemma 2.6 — Gaussian variance bound $0\preceq V^g\preceq 2I_m$
-- statement:
--   Let $|g\rangle$ be a pure Gaussian state for a CAR system on $n\ge2$ modes, and let
--   $$V^g=M^g-\mu^g(\mu^g)^{\mathsf T},$$
--   where $\mu^g$ and $M^g$ are the quadratic moments and quartic moment matrix of $|g\rangle\langle g|$. Then
--   $$0\preceq V^g\preceq 2I_m,$$
--   and for every $x\in\mathbb R^E$,
--   $$\operatorname{Var}_g(Q_x)=x^{\mathsf T}V^gx\le 2\|x\|^2 .$$
--
--   Gaussian states thus have uniformly bounded variance for every quadratic Hamiltonian of unit coefficient norm; this is the quantitative input of Lemma 3.1.
--
--   Differences from the source:
--   - encoding: $\|x\|^2$ → $\sum_p x_p^2$; $\operatorname{Var}_g(Q_x)$ → the real part of $\langle g|(Q_x-\langle Q_x\rangle_gI)^2|g\rangle$; reason: Euclidean norm; the variance of a Hermitian operator is real
-- source:
--   Ojas Parekh, Improved classical optimization of fermionic Hamiltonians beyond Gaussian states, STOC 2027 submission #390 (October 2026), source.pdf SHA-256 9018757e184cce1091160d8b5847294a0e6c16cc09386b1f2b6bb000f7542101, p.9, Lemma 2.6, eq. (2.11)

import Mathlib
import Definitions.Def_QuarticGauss390_EigenBound_CAR
import Definitions.Def_QuarticGauss390_EigenBound_Gaussian
import Definitions.Def_QuarticGauss390_EigenBound_Moments

open Matrix

namespace QuarticGauss390.EigenBound

/-- Lemma 2.6, p.9 (Gaussian variance bound): for a Gaussian `|g⟩` and
`V^g = M^g - μ^g (μ^g)ᵀ`, `0 ⪯ V^g ⪯ 2 I_m`, and for every `x ∈ ℝ^E`,
`Var_g(Q_x) = xᵀ V^g x ≤ 2 ‖x‖²`. -/
theorem lemma_2_6 {n : ℕ} (hn : 2 ≤ n) (C : CAR n) (g : Vec n) (hg : IsGaussian C g) :
    let μ := quadMoments C (pureProj g)
    let V := momentMatrix C (pureProj g) - vecMulVec μ μ
    V.PosSemidef ∧
    ((2 : ℝ) • (1 : Matrix (Pair n) (Pair n) ℝ) - V).PosSemidef ∧
    (∀ x : Pair n → ℝ,
      variance (pureProj g) (quadHam C x) = x ⬝ᵥ (V *ᵥ x) ∧
      x ⬝ᵥ (V *ᵥ x) ≤ 2 * ∑ p, x p ^ 2) := by sorry

end QuarticGauss390.EigenBound
