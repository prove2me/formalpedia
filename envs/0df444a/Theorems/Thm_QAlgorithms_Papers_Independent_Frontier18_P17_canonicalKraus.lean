-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P17_canonicalKraus
-- name    : QAlgorithms.Papers.Independent.Frontier18.P17.canonicalKraus
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:32:00.406907+00:00
-- url     : https://prove2.me/theorems/35a73c52-369f-4115-9284-5eaf91a98ffa
-- title:
--   Canonical Kraus decomposition from positive singular data
-- statement:
--   Let $N\ge1$ and let $\Phi:M_N(\mathbb C)\to M_N(\mathbb C)$ be a complex-linear completely positive trace-preserving map, as in Section IV. Define $D_{(a,i),(b,j)}=\Phi(E_{ij})_{ab}$. There exist $k\le N^2$, positive real numbers $\sigma_i$, and an orthonormal family $v_i\in\mathbb C^{N^2}$ giving the full positive spectral/singular decomposition of $D$. With $\kappa_i=\operatorname{unres}(v_i)$, these data satisfy
--
--   $$D=\sum_{i=1}^k\sigma_i v_i v_i^\dagger,\qquad
--   \Phi(\rho)=\sum_{i=1}^k\sigma_i\kappa_i\rho\kappa_i^\dagger\quad\text{for every density matrix }\rho.$$
--
--   This constructs canonical Kraus operators $\sqrt{\sigma_i}\kappa_i$ from the dynamical matrix. The singular data are existential conclusions and are fixed before the input state is quantified.
-- source:
--   Singular value decomposition and matrix reorderings in quantum information theory, arXiv:1011.1585v2, PDF p. 7, Theorem 7, Eq.(48)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct

namespace QAlgorithms.Papers.Independent.Frontier18.P17

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap depolarizing)

open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

/-- PDF p.7, Theorem 7, Eq. (48): produce the canonical Kraus data, rather
than assuming a decomposition. The positive dynamical matrix has identical left
and right singular systems. Scope is CPTP as specified in the section. -/
theorem canonicalKraus {N : ℕ} (hN : 0 < N)
    (Phi : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ)
    (hPhi : CPTP Phi) :
    ∃ (k : ℕ) (s : Fin k → ℝ)
      (v : Fin k → EuclideanSpace ℂ (Fin N × Fin N)),
      k ≤ N*N ∧ ThinSVD (dynamical Phi) s v v ∧
      ∀ rho, QAlgorithms.IsDensityMatrix rho →
        Phi rho = ∑ i, (s i : ℂ) • (unres (v i) * rho * (unres (v i))ᴴ) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P17

end
