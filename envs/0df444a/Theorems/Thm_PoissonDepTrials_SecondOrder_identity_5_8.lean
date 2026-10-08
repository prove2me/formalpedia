-- Prove2me | Theorems.Thm_PoissonDepTrials_SecondOrder_identity_5_8
-- name    : PoissonDepTrials.SecondOrder.identity_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:51:46.442457+00:00
-- url     : https://prove2.me/theorems/03c1b4d7-0e18-4fb9-a5d2-9025132dccf8
-- title:
--   (5.8), p. 544 — for independent trials, Eh(W) = 𝒫_λh − Σ_i p_i² E U_λh(W^{(i)})
-- statement:
--   Let $X_1,\dots,X_n$ be independent Bernoulli trials with $p_i=P(X_i=1)$, $\lambda=\sum_i p_i>0$, $W=\sum_iX_i$ and $W^{(i)}=\sum_{k\ne i}X_k$. For every bounded $h$ on the nonnegative integers,
--   $$Eh(W)=\mathscr P_\lambda h-\sum_{i=1}^n p_i^2\,E\,U_\lambda h\bigl(W^{(i)}\bigr).$$
--
--   This is the first-order identity (2.6) specialised to independent trials ($m=0$); applying it a second time to $EU_\lambda h(W^{(i)})$ produces the second-order term of Theorem 5.1.
--
--   **Formalization Note** The page writes $nEp_I^2E^IU_\lambda h(W^*)$ with a random index $I$ uniform on $\{1,\dots,n\}$ and independent of the trials, and $W^*=\sum_{i\ne I}X_i$; this equals $\sum_ip_i^2EU_\lambda h(W^{(i)})$, the form stated here (the random indices are, in the paper's words, a device so that "the use of symbols may be simplified"). The trials are a sequence $X:\mathbb N\to\Omega\to\mathbb N$ with $X_i\in\{0,1\}$ almost surely and $X_i\equiv0$ for $i=0$ and $i>n$, the paper's own padding convention (p. 535); constants generate the trivial $\sigma$-algebra, so independence of the padded family is independence of $X_1,\dots,X_n$. $\lambda>0$ is added because $U_\lambda$ divides by $\lambda$. $\|h\|$ is replaced by a bound $M$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 544, proof of Theorem 5.1, (5.8)

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- (5.8), proof of Theorem 5.1, p. 544, in index form: for independent Bernoulli trials,
`Eh(W) = 𝒫_λh − Σ_{i=1}^n p_i² E U_λh(W^{(i)})`. -/
theorem identity_5_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (hind : iIndepFun (fun i => X i) P)
    (hlam : 0 < lam P n X) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∫ ω, h (W n X ω) ∂P = poissonExp (lam P n X) h -
      ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 * ∫ ω, stU (lam P n X) h (Wi n X i ω) ∂P := by sorry

end PoissonDepTrials.SecondOrder
