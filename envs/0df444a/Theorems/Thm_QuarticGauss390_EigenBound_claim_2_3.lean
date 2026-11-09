-- Prove2me | Theorems.Thm_QuarticGauss390_EigenBound_claim_2_3
-- name    : QuarticGauss390.EigenBound.claim_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:31.075092+00:00
-- url     : https://prove2.me/theorems/9b012cec-0525-4813-ab98-3cd2bdd57278
-- title:
--   Claim 2.3 — the coefficient matrix $C^R$: zero on overlapping pairs, $\mathrm{Tr}[(C^R)^2]=6s^2$, $H_{C^R}=6R$, $\tau[Rq_pq_r]=C^R_{pr}$
-- statement:
--   Let $R=\sum_{|S|=4}r_Sc_S$ be a homogeneous quartic Majorana operator with real coefficients on $n\ge2$ modes, let $C^R=M^{2^{-n}R}$ be its coefficient matrix and $s^2=\tau[R^2]$. Then
--
--   1. $C^R_{pr}=0$ whenever the pairs $p,r$ share an index (in particular when $p=r$);
--   2. $$\operatorname{Tr}[(C^R)^2]=6s^2;$$
--   3. $$H_{C^R}=6R;$$
--   4. $\tau[Rq_pq_r]=C^R_{pr}$ for all $p,r\in E$.
--
--   The claim identifies $C^R/6$ as a coefficient matrix that represents $R$, with Frobenius norm controlled by $\tau[R^2]$.
--
--   Differences from the source:
--   - encoding: $s=\sqrt{\tau[R^2]}$ → $\sigma(R)=\sqrt{\operatorname{Re}\tau[R^2]}$, used squared; reason: $\tau[R^2]$ is real and nonnegative, so $\sigma(R)^2=\tau[R^2]$
--   - encoding: "p, r share an index" → one of the four coordinate equalities between $p=(i,j)$ and $r=(k,\ell)$; reason: same condition, includes $p=r$
-- source:
--   Ojas Parekh, Improved classical optimization of fermionic Hamiltonians beyond Gaussian states, STOC 2027 submission #390 (October 2026), source.pdf SHA-256 9018757e184cce1091160d8b5847294a0e6c16cc09386b1f2b6bb000f7542101, p.7, Claim 2.3, eq. (2.6a)–(2.6c), with Definition 2.2

import Mathlib
import Definitions.Def_QuarticGauss390_EigenBound_CAR
import Definitions.Def_QuarticGauss390_EigenBound_Moments

open Matrix

namespace QuarticGauss390.EigenBound

/-- Claim 2.3, p.7: for a homogeneous quartic `R = ∑_{|S|=4} r_S c_S` with real coefficients,
`C = C^R` and `s² = τ[R²]`: `C_{pr} = 0` whenever `p, r` share an index;
`Tr[C²] = 6 s²`; `H_C = 6 R`; `τ[R q_p q_r] = C_{pr}`. -/
theorem claim_2_3 {n : ℕ} (hn : 2 ≤ n) (C : CAR n) (r : Finset (Fin (2 * n)) → ℝ) :
    let R := quartic C r
    let Cm := coefMatrix C R
    (∀ p q : Pair n, (p.1.1 = q.1.1 ∨ p.1.1 = q.1.2 ∨ p.1.2 = q.1.1 ∨ p.1.2 = q.1.2) →
      Cm p q = 0) ∧
    (Cm * Cm).trace = 6 * sigma n R ^ 2 ∧
    coefHam C Cm = (6 : ℂ) • R ∧
    (∀ p q : Pair n, normTrace n (R * qOp C p * qOp C q) = ((Cm p q : ℝ) : ℂ)) := by sorry

end QuarticGauss390.EigenBound
