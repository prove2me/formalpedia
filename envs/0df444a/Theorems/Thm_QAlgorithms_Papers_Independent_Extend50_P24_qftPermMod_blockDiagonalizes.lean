-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P24_qftPermMod_blockDiagonalizes
-- name    : QAlgorithms.Papers.Independent.Extend50.P24.qftPermMod_blockDiagonalizes
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:47:27.746658+00:00
-- url     : https://prove2.me/theorems/5c842ab4-f305-4097-8477-7bcddaf431f2
-- title:
--   Uniform padded block diagonalization of permutation modules
-- statement:
--   Let $n\geq1$. A type $T$ is specified by its sorted word $E_0(T)$ on an alphabet of at most $n$ letters, with zero letter counts allowed. Let $Y_T\leq S_n$ be its stabilizer, and let $\mathcal W_T$ be the orbit of $E_0(T)$. The word basis of $\mathbb C[\mathcal W_T]$ is identified with the fixed-transversal coset basis. Define the normalized coset embedding and its Fourier transform by
--
--   $$
--   J_T|w\rangle=\frac{1}{\sqrt{|Y_T|}}
--   \sum_{g:E_0(T)\circ g^{-1}=w}|g\rangle,\qquad M_T=F_nJ_T.
--   $$
--
--   The exact action of the displayed QFTPermMod circuit on these embedded inputs is $M_T$, with a trivial coherent GPE ancillary label. It satisfies
--
--   $$
--   M_T^\dagger M_T=I,\qquad
--   M_TP_T(g)v=\left(\bigoplus_{\lambda\vdash n}\rho_\lambda(g)\otimes I\right)M_Tv
--   \quad\text{for every }g\in S_n,\ v\in\mathbb C[\mathcal W_T],
--   $$
--
--   where $P_T(g)$ permutes tensor positions in the module words. There are Young realizations fixed for each $n$, a single classical polynomial-time constructor taking $T,n,t$, and one polynomial $p$, uniform over all types. For every $t\geq1$ the resulting finite-gate circuit has work at most $p(1+n+t)$ and approximates $M_T$ with operator-norm error at most $2^{-t}$, including ancillary leakage. Taking $t=\lceil\log_2(1/\epsilon)\rceil$ yields the stated polynomial dependence for every $0<\epsilon<1$.
--
--   This is padded block diagonalization. A clean computational SSYT multiplicity basis is a distinct source assertion and is deferred.
-- source:
--   An efficient high dimensional quantum Schur transform, arXiv:1804.00055v2, PDF p. 13, Theorem 1: QFTPermMod block diagonalizes a permutation module

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P24

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Extend50.P24

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Renew46.P26 (boxContent)

/-- Theorem 1, PDF pp.13-15: QFTPermMod block diagonalizes every type with
one polynomial bound uniform in the type. The target is padded F J_T;
no computational SSYT multiplicity-label conclusion is added. -/
theorem qftPermMod_blockDiagonalizes :
    ∃ Y : (n : ℕ) → SymmetricModels n,
      (∀ n, 0 < n → IsUnitaryBetween (symmetricFourier (Y n))) ∧
      ∃ circuits : (n : ℕ) → PermutationType n → ℕ → CompiledCircuit,
      ∃ p : Polynomial ℕ, ∃ generate : List Bool → List Bool,
        QAlgorithms.Complexity.PolyTimeComputable generate ∧
        ∀ n (T : PermutationType n) t, 0 < n → 0 < t →
          let M := qftPermMod (Y n) T
          Mᴴ * M = 1 ∧
          (∀ g (v : EuclideanSpace ℂ (ModuleWord T)),
            applyMatrix M (QAlgorithms.act (moduleAction T g) v) =
              youngFourierAction (Y n) g (applyMatrix M v)) ∧
          generate (moduleRequest T t) = (circuits n T t).code ∧
          (circuits n T t).work ≤ p.eval (1 + n + t) ∧
          Approximates (fun w => moduleWordCode w.val) symmetricCode M
            (circuits n T t) ((2 : ℝ) ^ (-(t : ℤ))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P24

end
