-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P18_localIsometricInvariance
-- name    : QAlgorithms.Papers.Independent.Dependency50.P18.localIsometricInvariance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:56:58.629446+00:00
-- url     : https://prove2.me/theorems/75caa00a-a4b9-4005-bc67-2bb6f38c24ff
-- title:
--   Local isometric invariance
-- statement:
--   All systems are finite-dimensional and nonzero, with fixed orthonormal product bases, and logarithms are base two. States are positive semidefinite matrices of trace one. For a positive bipartite operator $s$, define $\gamma(s)$ as the infimum of $\operatorname{Tr}(K_A\otimes L_B)$ over Hermitian $K_A,L_B,V_{AB}$ satisfying $T_B(V_{AB}\pm s)\ge0$ and $K_A\otimes L_B\pm V_{AB}\ge0$, with both signs required. Here $T_B$ transposes only Bob's system. Set $C_\gamma(s)=\log_2\gamma(s)$, with $\log_2 0=-\infty$.
--
--   Let $D$ be a dimension-compatible extended-real generalized divergence satisfying data processing for every CPTP channel, $D(r\|cs)=D(r\|s)-\log_2c$ for $c>0$, and $D(r\|r)=0$. Comparisons need not be normalized and divergence values are not truncated to be nonnegative. Write
--   $$\Gamma_D(r)=\inf_{s\ge0:\,\gamma(s)\le1}D(r\|s).$$
--
--   Let $U:A\to A'$ and $V:B\to B'$ be rectangular isometries, so $U^\dagger U=I_A$ and $V^\dagger V=I_B$, and write $\mathcal U(s)=UsU^\dagger$, $\mathcal V(t)=VtV^\dagger$. For all positive $s$ and all states $r$,
--   $$C_\gamma(s)=C_\gamma((\mathcal U\otimes\mathcal V)(s)),\qquad
--   \Gamma_D(r)=\Gamma_D((\mathcal U\otimes\mathcal V)(r)).$$
--
--   The output dimensions may be larger. This gives invariance under local embeddings.
-- source:
--   Upper Bounds on the Distillable Randomness of Bipartite Quantum States, arXiv:2212.09073v1, PDF p. 2, Corollary 3, (10)–(11)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

/-- Corollary 3, PDF pp.2–3, (10)–(11). The printed common PSD domain is corrected:
Gamma requires a state by (4) and the proof. Rectangular isometries can enlarge dimensions. -/
theorem localIsometricInvariance (D : Divergence) (hD : IsGeneralizedDivergence D)
    (U : Matrix C A ℂ) (V : Matrix E B ℂ) (hU : Matrix.conjTranspose U * U = 1) (hV : Matrix.conjTranspose V * V = 1) :
    (∀ sigma : Matrix (A × B) (A × B) ℂ, sigma.PosSemidef →
      cGamma sigma = cGamma (QAlgorithms.Papers.Independent.Information100.P62.tensorChannel (QAlgorithms.conjSuperop U)
        (QAlgorithms.conjSuperop V) sigma)) ∧
    (∀ rho : Matrix (A × B) (A × B) ℂ, QAlgorithms.IsDensityMatrix rho →
      capitalGamma D rho = capitalGamma D (QAlgorithms.Papers.Independent.Information100.P62.tensorChannel (QAlgorithms.conjSuperop U)
        (QAlgorithms.conjSuperop V) rho)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P18

end
