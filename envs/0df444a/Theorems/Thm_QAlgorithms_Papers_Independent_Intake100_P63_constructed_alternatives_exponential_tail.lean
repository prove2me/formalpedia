-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_constructed_alternatives_exponential_tail
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.constructed_alternatives_exponential_tail
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:24:03.203104+00:00
-- url     : https://prove2.me/theorems/c4714f32-117a-4a45-b63e-eaec20778111
-- title:
--   Lemma III.9: uniform exponential tail for constructed almost-power alternatives
-- statement:
--   Let $H$ be a nonzero finite-dimensional complex Hilbert space and let $\rho\in\mathcal D(H)$ be a normalized density operator. For each positive integer $n$, let $M_n\subseteq\mathcal D(H^{\otimes n})$ be closed and convex. Assume that one fixed full-rank state $\sigma$ has $\sigma^{\otimes n}\in M_n$ for every positive $n$, that every single-copy partial trace preserves the family, that tensor products map $M_n\times M_m$ into $M_{n+m}$, and that conjugation by every copy permutation preserves $M_n$. Define $E_{M_n}(\xi)=\inf_{\omega\in M_n}D_2(\xi\Vert\omega)$, using base-two relative entropy with value $+\infty$ on failed support inclusion, and define $E_M^\infty(\rho)=\inf_{n\ge1}E_{M_n}(\rho^{\otimes n})/n$.
--
--   Let $\theta\in H\otimes H_E$ be a unit vector, with $H_E$ a copy of the nonzero finite-dimensional space $H$, and put $\rho=\operatorname{Tr}_E|\theta\rangle\langle\theta|$, assuming $\lambda_{\max}(\rho)<1$. For $N=n-m$, use the normalized symmetric expansion
--   $$
--   \Psi_{n,m,r}=\sum_{k=0}^{r}\beta_k\operatorname{Sym}(\eta_k\otimes\theta^{\otimes(N-k)}),\qquad \sum_k|\beta_k|^2=1,
--   $$
--   where every active $\eta_k$ is normalized, symmetric, and lies in $(\theta^\perp)^{\otimes k}$, and $\operatorname{Sym}$ denotes normalized symmetrization. Define the unnormalized vector $\Phi_{n,m,r}$ by retaining exactly the terms with $|\beta_k|\ge1/n$. Whenever this vector is nonzero, set $\pi_n=\operatorname{Tr}_{1,\ldots,r}\operatorname{Tr}_E|\Phi_{n,m,r}\rangle\langle\Phi_{n,m,r}|/\|\Phi_{n,m,r}\|^2$.
--
--   Let $m=m(n)$ and $r=r(n)$ satisfy $m+r\le n$ for positive $n$, with $m,r=o(n)$; the normalized cutoff reduction is defined eventually from these data. Choose a relative-entropy minimizer $\widetilde\omega_n\in M_{n-m-r}$ for $\pi_n$, and for a fixed $\tau>0$ set
--   $$
--   \omega_n=\frac1{1+\tau}\widetilde\omega_n+\frac\tau{1+\tau}\sigma^{\otimes(n-m-r)}.
--   $$
--   Here sigma is any fixed full-rank witness of the family. Given $\nu>0$ and thresholds $\lambda_n\ge D_2(\pi_n\Vert\omega_n)+\nu n$ on the eventual normalized domain, there exist $\gamma>0$, a sequence of integers $\ell_n$, and $N$ such that
--   $$
--   \operatorname{Tr}(\pi_n^{\otimes l}-2^{\lambda_n l}\omega_n^{\otimes l})_+
--   \le2^{-\gamma n l}\qquad(n\ge N,\ l\ge\ell_n,\ n,l\ge1).
--   $$
--
--   The alternatives and reductions are constructed objects. Gamma is uniform in both n and l, while the block threshold may depend on n; no variance bound from the proof is assumed.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 21, Lemma III.9: uniform exponential tail for constructed almost-power alternatives

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P63

open QAlgorithms Filter Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat relativeBits)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Advance50.P30 (joinCopies defectTensor)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.21 Lemma III.9 Eq.(124): the actual cutoff reductions and Eq.(122)
alternatives, with gamma uniform over n and l. The threshold l_n may depend on n. -/
theorem constructed_alternatives_exponential_tail {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (M : (n : ℕ) → Set (Mat (Copies I n))) (hM : stateSetAxioms M)
    (theta : Vec (I × I)) (htheta : IsState theta) (hmixed : MixedMarginal theta)
    (m r : ℕ → ℕ) (hm : Sublinear m) (hr : Sublinear r)
    (hrange : ∀ n, 0 < n → m n + r n ≤ n)
    (D : (n : ℕ) → Expansion theta (n - m n) (r n))
    (sigma : Mat I) (hsigma : IsDensityMatrix sigma)
    (hfull : LinearMap.ker sigma.mulVecLin = ⊥)
    (hwitness : ∀ n, 0 < n → piKron n sigma ∈ M n)
    (tau nu : ℝ) (htau : 0 < tau) (hnu : 0 < nu) (lambda : ℕ → ℝ)
    (hlambda : ∀ᶠ n in atTop,
      (relativeBits (cutoffReduction (D n) n)
        (regularizedAlternative (M (n - m n - r n)) (cutoffReduction (D n) n) sigma tau) : EReal) +
          ((nu * n : ℝ) : EReal) ≤ (lambda n : EReal)) :
    ∃ gamma : ℝ, 0 < gamma ∧ ∃ ell : ℕ → ℕ, ∃ N : ℕ,
      ∀ n, N ≤ n → 0 < n → ∀ l, ell n ≤ l → 0 < l →
        (positivePart (piKron l (cutoffReduction (D n) n) -
          (((2 : ℝ) ^ (lambda n * l) : ℝ) : ℂ) •
            piKron l (regularizedAlternative (M (n - m n - r n))
              (cutoffReduction (D n) n) sigma tau))).trace.re ≤
          (2 : ℝ) ^ (-gamma * n * l) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
