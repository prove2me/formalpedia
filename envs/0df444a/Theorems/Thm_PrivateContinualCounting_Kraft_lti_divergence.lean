-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_lti_divergence
-- name    : PrivateContinualCounting.Kraft.lti_divergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:12.337645+00:00
-- url     : https://prove2.me/theorems/91e8f47d-6f6f-4af7-821f-329578ff0a65
-- title:
--   Theorem 3.1 — real, complex, vector and periodic divergence
-- statement:
--   Let $m\ge1$ and let $(l_j,r_k)$ be scalar or $m$-vector LTI factors with real or complex coefficients. Their bilinear convolution equals $1$ at every nonnegative coefficient index and $\Delta^2=\sum_k\|r_k\|_2^2<\infty$. Set $E_t=\sum_{j<t}\|l_j\|_2^2$ and $v_t=\Delta^2E_t$. Then
--   $$\frac{E_t}{(\ln t)^2}\longrightarrow+\infty,\qquad
--   \frac{v_t}{(\ln t)^2}\longrightarrow+\infty.$$
--   For complex coefficients the realification $[\Re l,-\Im l]$, $[\Re r;\Im r]$ is admissible and preserves every $E_t$ and $\Delta^2$, so the variance is that of an actually released real counter. For every fixed-period counter with a countable internal index set, its normalized variance has the same divergence over all times; the phase-row energies $E_{a,n}$ diverge after division by $(\ln n)^2$ in block time. No envelope assumption or restriction on signs is made. This full statement is the source's common obstruction for the goal's first clause and its necessity argument.
--
--   Differences from the source:
--   - encoding: scalar/vector norms and bilinear convolution over ℝ or ℂ → separate universal real and complex clauses with Euclidean squared coordinate norms; reason: Both fields and every finite positive dimension are retained; no Hermitian pairing is substituted.
--   - encoding: fixed-period Gaussian counters with arbitrary countable inner coordinates → PeriodicCounter p I₀ contains the full square-summable factorisation and measurable L² decoder sums on the canonical independent Gaussian seed; reason: Every source counter is represented in law; the block Toeplitz identities include every phase and no within-block cutoff. The period is fixed before time varies.
--   - generalization: Theorem 3.1 asserts only the energy and variance limits; the complex and periodic reductions are stated in Appendix A → the realification admissibility and norm identities and all phase-energy limits are additional conclusions; reason: They are Appendix A's own claims (printed 18 / PDF 20) and the conjunction specializes to Theorem 3.1's complete claim by dropping them.
--   - encoding: vₜ/(ln t)² tends to infinity → Tendsto of the quotient from natural-number atTop to real atTop; reason: This means eventually exceeding every real threshold along all times; the total log and division at t=0,1 affect no limit.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 7, PDF p. 9, Theorem 3.1; Kisung Park, STOC 2027 submission #86 (October 2026), p. 18, PDF p. 20, Appendix A, realification and phase-energy argument

import Definitions.Def_PrivateContinualCounting_Kraft_LTIFactors
import Definitions.Def_PrivateContinualCounting_Kraft_PeriodicCounter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft

/-- Theorem 3.1 including the full real/complex vector and fixed-period clauses.
The complex variance is that of the released realification in Appendix A. -/
theorem lti_divergence :
    (∀ (m : ℕ) (d : LTIData ℝ m), IsLTI d →
      LogSqDiverges d.energy ∧ LogSqDiverges d.variance) ∧
    (∀ (m : ℕ) (d : LTIData ℂ m), IsLTI d →
      LogSqDiverges d.energy ∧ LogSqDiverges d.variance ∧
      IsLTI (realify d) ∧ (∀ t, (realify d).energy t = d.energy t) ∧
      (realify d).deltaSq = d.deltaSq) ∧
    (∀ (p : ℕ) (I₀ : Type) [Countable I₀] (M : PeriodicCounter p I₀),
      (∀ a : Fin p, LogSqDiverges (M.phaseEnergy a)) ∧
      LogSqDiverges M.counter.variance) := by sorry

end PrivateContinualCounting.Kraft
