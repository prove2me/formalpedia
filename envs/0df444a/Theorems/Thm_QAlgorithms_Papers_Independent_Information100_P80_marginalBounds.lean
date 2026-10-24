-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P80_marginalBounds
-- name    : QAlgorithms.Papers.Independent.Information100.P80.marginalBounds
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:15:46.711877+00:00
-- url     : https://prove2.me/theorems/2210abe1-2275-4b49-83e2-fe23586ea477
-- title:
--   Lemma 1 (Marginal bounds), all clauses (i)–(iii)
-- statement:
--   All registers below have positive finite dimension, and $X\preceq Y$ means that $Y-X$ is positive semidefinite. Operators on omitted subsystems act as the identity.
--
--   1. Let $S_{BE}\succeq0$ and let $K:B\to B'$ satisfy $K^\dagger K\preceq I_B$. Then
--   $$
--   \operatorname{tr}_{B'}[(K\otimes I_E)S_{BE}(K^\dagger\otimes I_E)]
--   \preceq\operatorname{tr}_B S_{BE}.
--   $$
--   2. Let $Q_{BR}\succeq0$ and $\rho_{BER}\succeq0$, without trace normalization. Define $\tau_E=\operatorname{tr}_{BR}(Q^{1/2}\rho Q^{1/2})$ and $c=\|\operatorname{tr}_R Q\|_\infty$, where the square root is the PSD square root and the norm is the spectral norm. Then
--   $$
--   \operatorname{tr}_B(Q\rho Q)\preceq c\,\tau_E\otimes I_R.
--   $$
--   3. For arbitrary vectors $v_1,\ldots,v_m$ in any finite-dimensional register and real weights $p_j\ge0$ with $\sum_jp_j=1$,
--   $$
--   \left|\sum_jp_jv_j\right\rangle\left\langle\sum_jp_jv_j\right|
--   \preceq\sum_jp_j|v_j\rangle\langle v_j|.
--   $$
--
--   These inequalities control marginals after contractions, positive filters, and convex combinations. The vectors need not be unit vectors, and zero operators and vectors are permitted.
-- source:
--   Strong Converses for Quantum Channel Capacities from Blowing-Up Lemmata, arXiv:2609.11771v1, PDF p. 5, Lemma 1 (Marginal bounds), all clauses (i)–(iii)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P80

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

/-- Lemma 1 (all three clauses), PDF pp.5–6, (8)–(11).
All matrix comparisons are Loewner comparisons; no trace or vector normalization is imposed. -/
theorem marginalBounds
    {B Bprime E R V : Type*} [Fintype B] [Fintype Bprime] [Fintype E]
    [Fintype R] [Fintype V] [DecidableEq B] [DecidableEq Bprime]
    [DecidableEq E] [DecidableEq R]
    [Nonempty B] [Nonempty Bprime] [Nonempty E] [Nonempty R] [Nonempty V] :
    (∀ (S : Matrix (B × E) (B × E) ℂ) (K : Matrix Bprime B ℂ),
      S.PosSemidef → OperatorLE (Kᴴ * K) 1 →
      OperatorLE
        (traceLeft (Matrix.kronecker K (1 : Matrix E E ℂ) * S *
          (Matrix.kronecker K (1 : Matrix E E ℂ))ᴴ)) (traceLeft S)) ∧
    (∀ (Q : Matrix (B × R) (B × R) ℂ)
      (rho : Matrix (B × (E × R)) (B × (E × R)) ℂ),
      Q.PosSemidef → rho.PosSemidef →
      let L := liftBR (E := E) Q
      let H := liftBR (E := E) (cfc Real.sqrt Q)
      let tau := traceBR (H * rho * H)
      let c := specNorm (traceRight Q)
      OperatorLE (traceLeft (L * rho * L))
        (c • Matrix.kronecker tau (1 : Matrix R R ℂ))) ∧
    (∀ (m : ℕ) (v : Fin m → EuclideanSpace ℂ V) (p : Fin m → ℝ),
      (∀ j, 0 ≤ p j) → (∑ j, p j) = 1 →
      OperatorLE (pureDensity (∑ j, (p j : ℂ) • v j))
        (∑ j, p j • pureDensity (v j))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P80

end
