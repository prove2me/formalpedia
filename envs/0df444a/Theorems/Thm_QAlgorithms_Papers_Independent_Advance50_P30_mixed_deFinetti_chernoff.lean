-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P30_mixed_deFinetti_chernoff
-- name    : QAlgorithms.Papers.Independent.Advance50.P30.mixed_deFinetti_chernoff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:52:46.019858+00:00
-- url     : https://prove2.me/theorems/5915612f-8b51-4bcd-acc4-673dc3ad3263
-- title:
--   Theorem 1: mixed de Finetti approximation with full and reduced Chernoff estimates
-- statement:
--   Let $\mathcal H$ be a finite-dimensional complex Hilbert space of dimension $d\ge1$, with a fixed orthonormal basis. All states below are positive operators of trace one; pure states are unit vectors. Write $\|\cdot\|_1$ for the full trace norm (the full $\ell_1$ norm for classical distributions), $H_2$ for binary entropy in bits, and define
--   $$
--   e(\delta,N,r,w)=2^{-N[\delta^2/4-H_2(r/N)]+w\log_2(N/2+1)}.
--   $$
--
--   Let $n,k\ge1$, $0\le r\le n$, and let $\rho_{n+k}$ be invariant under every permutation of its sites. Then there exist a Borel probability measure $\mu$ on the single-site density operators and a measurable, integrable family $\tau_\sigma$ of normalized mixed almost-power states along $\sigma$, such that
--   $$
--   \left\|\operatorname{Tr}_k\rho_{n+k}-\int\tau_\sigma\,d\mu(\sigma)\right\|_1
--   \le 2\exp\!\left[-\frac{k(r+1)}{2(n+k)}+\frac{d^2}{2}\ln k\right].
--   $$
--   For every $\sigma$, every finite normalized POVM $M=\{M_a\}_{a=1}^w$, and every $\delta>0$, write $P_M(\sigma)_a=\operatorname{Tr}(\sigma M_a)$ and $Q_M$ for the normalized empirical frequencies from measuring $M$ on each site. If $2r\le n$, then
--   $$
--   \Pr_{\tau_\sigma}\{\|P_M(\sigma)-Q_M\|_1>\delta\}\le e(\delta,n,r,w).
--   $$
--   For every $1\le n'\le n$ with $2r\le n'$, the same probability on the $n'$-site reduced state is at most $e(\delta,n',r,w)$.
--
--   Mixed almost-power states are obtained by tracing the reference systems of convex mixtures of pure almost-power states along a unit purification of $\sigma$. Pure almost-power means unit vectors in the symmetric subspace intersected with the span of permutations of $\theta^{\otimes(n-r)}\otimes\psi_r$. Thus the approximation family is specified geometrically, rather than by assuming the concentration conclusions. This result supplies finite parameter-estimation guarantees for invariant mixed inputs.
-- source:
--   Unconditional privacy over channels which cannot convey quantum information, arXiv:quant-ph/0702077v1, PDF p. 11, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P30

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixContinuousENorm

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixBorel

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.vectorMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.vectorBorel

/-- PDF pp.11--12, Theorem 1, Eqs.(7)--(9); construction on pp.15--16.
The source's proof supplies the half-length defect restrictions. At p.16 its
nprime-r superscript is read as the preserved defect count r, consistently
with Lemma 1 and the explicit restriction 2*r ≤ nprime.
Printed (8) has no half-length guard; changed to 2*r ≤ n for that clause
because its cited Lemma 2 requires this domain. The approximation clause
still permits every r ≤ n. -/
theorem mixed_deFinetti_chernoff {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (n k r : ℕ) (hn : 0 < n) (hk : 0 < k) (hr : r ≤ n)
    (rho : Op (Copies I (n + k))) (hrho : IsDensityMatrix rho)
    (hinv : InvariantCopyState rho) :
    ∃ (mu : Measure (DensityState I)) (family : DensityState I → Op (Copies I n)),
      IsProbabilityMeasure mu ∧ Measurable family ∧ Integrable family mu ∧
      (∀ sigma, AlmostAlong sigma n r (family sigma)) ∧
      traceNorm (reduceCopies rho n (by omega) - ∫ sigma, family sigma ∂mu) ≤
        deFinettiError n k r (Fintype.card I) ∧
      (2 * r ≤ n → ∀ (sigma : DensityState I) (w : ℕ), 0 < w →
        ∀ E : Fin w → Op I, IsPOVM E → ∀ delta : ℝ, 0 < delta →
          iidEvent (family sigma) E (fun out =>
            l1 (fun a => effectProb (E a) sigma.val) (empiricalFrequency out) > delta) ≤
              chernoffError delta n r w) ∧
      (∀ (np : ℕ) (hpos : 0 < np) (hle : np ≤ n), 2 * r ≤ np →
        ∀ (sigma : DensityState I) (w : ℕ), 0 < w →
        ∀ E : Fin w → Op I, IsPOVM E → ∀ delta : ℝ, 0 < delta →
          iidEvent (reduceCopies (family sigma) np hle) E (fun out =>
            l1 (fun a => effectProb (E a) sigma.val) (empiricalFrequency out) > delta) ≤
              chernoffError delta np r w) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P30

end
