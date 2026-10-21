-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P46_discreteExpurgated
-- name    : QAlgorithms.Papers.Independent.Renew46.P46.discreteExpurgated
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:56:00.452694+00:00
-- url     : https://prove2.me/theorems/811e1d48-c1da-43a3-b8d5-9394fbdc89c6
-- title:
--   §IV: discrete finite-block expurgated bound, (36)–(37)
-- statement:
--   Use normalized pure signals $S_i=|\psi_i\rangle\langle\psi_i|$, an admissible prior $\pi$ with defined finite expected real cost at most $E$, an affordable input, finite capacity $C$, integers $n,M\ge1$, and $R=\log M/n<C$. Let $s\ge1$, $p\ge0$, $\delta>0$, assume the double overlap series in the following formula has finite positive sum, and let $\nu_{n,\delta}>0$ be the probability under the independent product prior of $nE-\delta\le\sum_k f(i_k)\le nE$. Set
--
--   $$\widetilde\mu(\pi,s,p)=-s\log\sum_{i,k}\pi_i\pi_k e^{p[f(i)+f(k)-2E]}|\langle\psi_i,\psi_k\rangle|^{2/s}.$$
--
--   Then the infimal uniform-message average error under the per-word cost constraint satisfies
--
--   $$p(n,M)\le\exp\left\{-n\left[\widetilde\mu(\pi,s,p)-s\left(R+\frac2n\log\frac{2e^{p\delta}}{\nu_{n,\delta}}\right)\right]\right\}.$$
--
--   This is a finite-block expurgated bound, without discarding the shell term.
-- source:
--   On Quantum Communication Channels with Constrained Inputs, arXiv:quant-ph/9705054v1, PDF p. 12, §IV: discrete finite-block expurgated bound, (36)–(37)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P46

open Filter MeasureTheory QAlgorithms.RealRegisters

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section IV, PDF p.12, (36)-(37), constrained adaptation of [2], Prop.2.
The entire correction is (2/n) log(2 exp(p delta)/nu). -/
theorem discreteExpurgated {I A : Type} (S : A → constrainedCqState I)
    (hpure : ∀ a, ∃ psi : Hilbert I, ‖psi‖ = 1 ∧
      (S a).val = InnerProductSpace.rankOne ℂ psi psi)
    (f : A → ℝ) (E : ℝ) (hfeasible : ∃ a, f a ≤ E)
    (hfinite : constrainedCqCapacity S f E < ⊤) (pi : PMF A) (hpi : constrainedCqAdmissible f E pi)
    (n M : ℕ) (hn : 0 < n) (hM : 0 < M)
    (hR : ENNReal.ofReal (Real.log (M : ℝ) / (n : ℝ)) < constrainedCqCapacity S f E)
    (s p delta : ℝ) (hs : 1 ≤ s) (hp : 0 ≤ p) (hd : 0 < delta)
    (hdomain : expurgatedDiscreteDomain (fun a => (S a).val) pi f E s p)
    (hnu : 0 < shellDiscrete pi f E n delta) :
    constrainedCqError S f E n M ≤ Real.exp (-(n : ℝ) *
      (muExDiscrete (fun a => (S a).val) pi f E s p - s *
        (Real.log (M : ℝ) / (n : ℝ) + 2 / (n : ℝ) *
          Real.log (2 * Real.exp (p * delta) / shellDiscrete pi f E n delta)))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P46

end
