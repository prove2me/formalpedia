-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P46_discreteRandomCoding
-- name    : QAlgorithms.Papers.Independent.Renew46.P46.discreteRandomCoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:55:03.324145+00:00
-- url     : https://prove2.me/theorems/b133313c-a1b3-4641-a5d6-67e9e09a56cb
-- title:
--   §IV: discrete finite-block random-coding bound, (33)–(35)
-- statement:
--   Let $S_i=|\psi_i\rangle\langle\psi_i|$ be unit-vector pure signals of a discrete classical–quantum channel, with real cost $f$, real budget $E$, an affordable input and finite capacity $C$. Let $\pi$ be an admissible prior with defined finite mean cost at most $E$. Take integers $n,M\ge1$, $R=\log M/n<C$, parameters $0\le s\le1$, $p\ge0$, $\delta>0$, and work on the genuine convergence domain: the weighted coefficient series realize a bounded positive operator $T=\sum_i\pi_i e^{p(f(i)-E)}S_i$, and $T^{1+s}$ has finite positive trace. Let $\nu_{n,\delta}>0$ be the product-prior probability of $nE-\delta\le\sum_k f(i_k)\le nE$, and define
--
--   $$\mu(\pi,s,p)=-\log\operatorname{Tr}\left(\sum_i\pi_i e^{p(f(i)-E)}S_i\right)^{1+s}.$$
--
--   For the infimal uniform-message average error over collective codes satisfying the cost bound on every word,
--
--   $$p(n,M)\le 2\left(\frac{e^{p\delta}}{\nu_{n,\delta}}\right)^2e^{-n[\mu(\pi,s,p)-sR]}.$$
--
--   This finite-block bound makes no claim that the shell correction is subexponential.
-- source:
--   On Quantum Communication Channels with Constrained Inputs, arXiv:quant-ph/9705054v1, PDF p. 11, §IV: discrete finite-block random-coding bound, (33)–(35)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P46

open Filter MeasureTheory QAlgorithms.RealRegisters

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section IV, PDF p.11, (33)-(35), constrained adaptation of [2], Prop.1.
The prefactor is 2 times the squared quotient. Only a positive shell is assumed;
no shell asymptotic or reliability optimization is inferred. -/
theorem discreteRandomCoding {I A : Type} (S : A → constrainedCqState I)
    (hpure : ∀ a, ∃ psi : Hilbert I, ‖psi‖ = 1 ∧
      (S a).val = InnerProductSpace.rankOne ℂ psi psi)
    (f : A → ℝ) (E : ℝ) (hfeasible : ∃ a, f a ≤ E)
    (hfinite : constrainedCqCapacity S f E < ⊤) (pi : PMF A) (hpi : constrainedCqAdmissible f E pi)
    (n M : ℕ) (hn : 0 < n) (hM : 0 < M)
    (hR : ENNReal.ofReal (Real.log (M : ℝ) / (n : ℝ)) < constrainedCqCapacity S f E)
    (s p delta : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hp : 0 ≤ p) (hd : 0 < delta)
    (hdomain : randomDiscreteDomain (fun a => (S a).val) pi f E s p)
    (hnu : 0 < shellDiscrete pi f E n delta) :
    constrainedCqError S f E n M ≤ 2 * (Real.exp (p * delta) / shellDiscrete pi f E n delta) ^ 2 *
      Real.exp (-(n : ℝ) * (muDiscrete (fun a => (S a).val) pi f E s p -
        s * (Real.log (M : ℝ) / (n : ℝ)))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P46

end
