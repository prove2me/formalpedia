-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P28_wigner_eckart
-- name    : QAlgorithms.Papers.Independent.Gap48.P28.wigner_eckart
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:07:39.061728+00:00
-- url     : https://prove2.me/theorems/41f14219-45da-4be6-95f9-1a3b6a99eb94
-- title:
--   Wigner–Eckart factorization through the Clebsch–Gordan block
-- statement:
--   Let $d\ge1$ and let $Q_\mu^d,Q_\nu^d,Q_\lambda^d$ be polynomial unitary irreducible representations of $U(d)$, realized as the Young-image Schur modules for nonnegative partitions. Fix orthonormal coordinate bases of these spaces before choosing a tensor operator. Let $\{\alpha\}_{\alpha\in M}$ be a basis of the entire space $\operatorname{Hom}_{U(d)}(Q_\mu^d\otimes Q_\nu^d,Q_\lambda^d)$, normalized by $\alpha\beta^\dagger=\delta_{\alpha\beta}I_{Q_\lambda^d}$. Its adjoints determine the $\lambda$ block of the Clebsch–Gordan transform by the source convention $(U_{\rm CG}^{\mu,\nu})^\dagger|q_\lambda,\alpha^\dagger\rangle=\alpha^\dagger|q_\lambda\rangle$.
--
--   Suppose the components $T^\nu_{q_\nu}:Q_\mu^d\to Q_\lambda^d$ satisfy tensor covariance: for every $u\in U(d)$,
--   $r_\lambda(u)T^\nu_{q_\nu}r_\mu(u)^\dagger=\sum_{q'_\nu}r_\nu(u)_{q'_\nu,q_\nu}T^\nu_{q'_\nu}$.
--   There are complex scalars $\widehat T_\alpha$, independent of all three basis labels, such that
--
--   $$
--   \langle q_\lambda|T^\nu_{q_\nu}|q_\mu\rangle=
--   \sum_{\alpha\in M}\widehat T_\alpha
--   \langle q_\lambda,\alpha^\dagger|U_{\rm CG}^{\mu,\nu}|q_\mu,q_\nu\rangle.
--   $$
--
--   This exact identity separates invariant reduced coefficients from Clebsch–Gordan coefficients. It has no approximation or circuit-cost hypothesis.
-- source:
--   The Quantum Schur Transform: I. Efficient Qudit Circuits, arXiv:quant-ph/0601001v1, PDF p. 18, Theorem 1 (Wigner–Eckart), Eq.(45)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P28

open scoped Matrix Kronecker ComplexConjugate

/-- PDF p.18, Theorem 1 (Wigner–Eckart), Eq.(45), with covariance Eq.(38)
on p.17. All three modules are the actual polynomial U(d) Schur modules.
The multiplicity basis spans the entire intertwiner space and has the
coisometry normalization of p.13, rather than Hilbert–Schmidt unit norm.
The scalars are independent of all three basis labels. This is an exact
algebraic theorem, with no accuracy, gate, or n>=1 circuit hypotheses. -/
theorem wigner_eckart
    (d nMu nNu nLambda : ℕ) (hd : 1 ≤ d)
    (mu : QAlgorithms.Schur.Partition d nMu)
    (nu : QAlgorithms.Schur.Partition d nNu)
    (lambda : QAlgorithms.Schur.Partition d nLambda)
    {M N L A : Type*}
    [Fintype M] [DecidableEq M] [Nonempty M]
    [Fintype N] [DecidableEq N] [Nonempty N]
    [Fintype L] [DecidableEq L] [Nonempty L]
    [Fintype A] [DecidableEq A]
    (bMu : OrthonormalBasis M ℂ (QAlgorithms.Schur.schurModule mu))
    (bNu : OrthonormalBasis N ℂ (QAlgorithms.Schur.schurModule nu))
    (bLambda : OrthonormalBasis L ℂ (QAlgorithms.Schur.schurModule lambda))
    (b : Module.Basis A ℂ (intertwinerSpace
      (irrepMatrix mu bMu) (irrepMatrix nu bNu) (irrepMatrix lambda bLambda)))
    (hNormalization : ∀ a c : A,
      (b a).val * ((b c).val)ᴴ = if a = c then 1 else 0)
    (t : N → Matrix L M ℂ)
    (hCovariance : ∀ (u : Matrix.unitaryGroup (Fin d) ℂ) (qNu : N),
      irrepMatrix lambda bLambda u * t qNu *
          (irrepMatrix mu bMu u)ᴴ =
        ∑ qNuNext : N, (irrepMatrix nu bNu u qNuNext qNu) • t qNuNext) :
    ∃ reduced : A → ℂ, ∀ (qMu : M) (qNu : N) (qLambda : L),
      t qNu qLambda qMu =
        ∑ a : A, reduced a * cgBlockEntry b a qLambda qMu qNu := by sorry

end QAlgorithms.Papers.Independent.Gap48.P28

end
